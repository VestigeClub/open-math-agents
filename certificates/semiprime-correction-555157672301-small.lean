import FormalConjectures.OEIS.«247824»

/-!
# A part of the semiprime correction at 555,157,672,301

The certificate checks the prime-count differences for 832 primes
above 8,218 through 15,975. The quotient prime counts needed for those terms
lie between 34,751,653 and 67,545,646.
-/

/-
# A certified count of primes through 34,751,024

This auxiliary count anchors a segmented prime table. The finite tables in this file are proved correct by
induction. A square-cutoff form of Legendre's recurrence and a Meissel
semiprime correction reduce the numerical calculation to checked rows.
The Meissel identity comes from Physbuzz's published reduction for A247824.
The Legendre recursion adapts Daniel Veljjanoski's Palomar proof as formalized
by rleshner in OeisA100475.conjecture (Apache-2.0).
Palomar source: https://github.com/veljjanoski/oeis100475-palomar/tree/0968200356e449a24a023264821d4ea966091cf0
Reference: https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9315
-/

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


/- The Legendre and Meissel identities below are the public Physbuzz reduction
for OEIS A247824, itself crediting Daniel Veljjanoski and rleshner. This certificate supplies the base value for the next quotient interval. -/
open Finset
namespace RankWheel34751

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
  | p :: ps, t => if t < p then (if t=0 then 0 else 1) else
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
  by_cases sm : t < p
  · simp [List.foldr_cons,advance,evalPhi,sm]
  · by_cases short : t < (p+1)^2
    · have h := square_cut pos (by omega : p ≤ t) short
      rw [lst] at h
      rw [evalPhi,if_neg sm,if_pos short,ok t (by omega),ok p (by omega)]
      omega
    · simp only [List.foldr_cons,advance,evalPhi,if_neg sm,if_neg short,prev]

private def primeBit (tab : ℕ → ℕ) (n : ℕ) : Bool :=
  if n=0 then false else decide (tab (n-1) < tab n)

private theorem primeBit_eq {bound : ℕ} (tab : ℕ → ℕ)
    (ok : ∀ t, t ≤ bound → tab t = Nat.primeCounting t) (n : ℕ) (hn : n ≤ bound) :
    primeBit tab n = decide n.Prime := by
  cases n with
  | zero => simp [primeBit]
  | succ n =>
    simp only [primeBit,Nat.succ_ne_zero,if_false,Nat.succ_sub_one,ok n (by omega),ok _ hn]
    rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
        from Nat.count_succ Nat.Prime (n+1)]
    by_cases hp : (n+1).Prime <;> simp [hp]

private theorem filter_bits {bound : ℕ} (tab : ℕ → ℕ)
    (ok : ∀ t, t ≤ bound → tab t = Nat.primeCounting t) (p : ℕ) (hp : p ≤ bound) :
    (List.range (p+1)).filter (fun n => decide n.Prime) =
      (List.range (p+1)).filter (primeBit tab) := by
  apply List.filter_congr
  intro n hn
  have := List.mem_range.mp hn
  exact (primeBit_eq tab ok n (by omega)).symm

private theorem merge_filter (f : ℕ → Bool) (lo a b : ℕ) (l r : List ℕ)
    (hl : (List.range' lo a).filter f = l) (hr : (List.range' (lo+a) b).filter f = r) :
    (List.range' lo (a+b)).filter f = l++r := by
  rw [←List.range'_append_1,List.filter_append,hl,hr]

private theorem eval_delta (tab : ℕ → ℕ) (ps : List ℕ) (p n q old dec ans : ℕ)
    (le : p ≤ n) (sq : (p+1)^2 ≤ n) (div : n/p = q)
    (base : evalPhi tab ps n = old) (cut : evalPhi tab ps q = dec) (sub : old-dec=ans) :
    evalPhi tab (p::ps) n = ans := by
  rw [evalPhi,if_neg (not_lt.mpr le),if_neg (not_lt.mpr sq),div,base,cut,sub]

private theorem assemble {x y z a b r : ℕ} (hx : 1 ≤ x) (hy : y ≤ x) (cube : x < (y+1)^3)
    (sq : x < (z+1)^2) (zs : z*z ≤ x)
    (sieved : (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id x) +
      (Nat.primesLE y).card = a)
    (rows : (∑ p ∈ (Nat.primesLE z).filter (y < ·), (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = b)
    (total : 1+r+b=a) : Nat.primeCounting x=r := by
  exact rank_of_parts hx hy cube sq zs sieved rows total

private def ps0 : List ℕ := []
private theorem agree0 (t : ℕ) : ps0.foldr advance id t = evalPhi WheelTableA94.fast ps0 t := rfl

private theorem value0 : evalPhi WheelTableA94.fast ps0 34751024 = 34751024 := rfl

private def ps1 : List ℕ := 2 :: ps0
private theorem row1 :
    ((List.range (2+1)).filter (fun n => decide n.Prime)).reverse = ps1 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 2 (by decide)]
  decide +kernel
private theorem agree1 : ∀ t, ps1.foldr advance id t = evalPhi WheelTableA94.fast ps1 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row1 agree0 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut1 : evalPhi WheelTableA94.fast ps0 17375512 = 17375512 := by decide +kernel
private theorem value1 : evalPhi WheelTableA94.fast ps1 34751024 = 17375512 :=
  eval_delta WheelTableA94.fast ps0 2 34751024 17375512 34751024 17375512 17375512
    (by decide) (by decide) rfl value0 cut1 rfl

private def ps2 : List ℕ := 3 :: ps1
private theorem row2 :
    ((List.range (3+1)).filter (fun n => decide n.Prime)).reverse = ps2 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 3 (by decide)]
  decide +kernel
private theorem agree2 : ∀ t, ps2.foldr advance id t = evalPhi WheelTableA94.fast ps2 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row2 agree1 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut2 : evalPhi WheelTableA94.fast ps1 11583674 = 5791837 := by decide +kernel
private theorem value2 : evalPhi WheelTableA94.fast ps2 34751024 = 11583675 :=
  eval_delta WheelTableA94.fast ps1 3 34751024 11583674 17375512 5791837 11583675
    (by decide) (by decide) rfl value1 cut2 rfl

private def ps3 : List ℕ := 5 :: ps2
private theorem row3 :
    ((List.range (5+1)).filter (fun n => decide n.Prime)).reverse = ps3 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 5 (by decide)]
  decide +kernel
private theorem agree3 : ∀ t, ps3.foldr advance id t = evalPhi WheelTableA94.fast ps3 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row3 agree2 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut3 : evalPhi WheelTableA94.fast ps2 6950204 = 2316735 := by decide +kernel
private theorem value3 : evalPhi WheelTableA94.fast ps3 34751024 = 9266940 :=
  eval_delta WheelTableA94.fast ps2 5 34751024 6950204 11583675 2316735 9266940
    (by decide) (by decide) rfl value2 cut3 rfl

private def ps4 : List ℕ := 7 :: ps3
private theorem row4 :
    ((List.range (7+1)).filter (fun n => decide n.Prime)).reverse = ps4 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 7 (by decide)]
  decide +kernel
private theorem agree4 : ∀ t, ps4.foldr advance id t = evalPhi WheelTableA94.fast ps4 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row4 agree3 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut4 : evalPhi WheelTableA94.fast ps3 4964432 = 1323849 := by decide +kernel
private theorem value4 : evalPhi WheelTableA94.fast ps4 34751024 = 7943091 :=
  eval_delta WheelTableA94.fast ps3 7 34751024 4964432 9266940 1323849 7943091
    (by decide) (by decide) rfl value3 cut4 rfl

private def ps5 : List ℕ := 11 :: ps4
private theorem row5 :
    ((List.range (11+1)).filter (fun n => decide n.Prime)).reverse = ps5 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 11 (by decide)]
  decide +kernel
private theorem agree5 : ∀ t, ps5.foldr advance id t = evalPhi WheelTableA94.fast ps5 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row5 agree4 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut5 : evalPhi WheelTableA94.fast ps4 3159184 = 722099 := by decide +kernel
private theorem value5 : evalPhi WheelTableA94.fast ps5 34751024 = 7220992 :=
  eval_delta WheelTableA94.fast ps4 11 34751024 3159184 7943091 722099 7220992
    (by decide) (by decide) rfl value4 cut5 rfl

private def ps6 : List ℕ := 13 :: ps5
private theorem row6 :
    ((List.range (13+1)).filter (fun n => decide n.Prime)).reverse = ps6 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 13 (by decide)]
  decide +kernel
private theorem agree6 : ∀ t, ps6.foldr advance id t = evalPhi WheelTableA94.fast ps6 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row6 agree5 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut6 : evalPhi WheelTableA94.fast ps5 2673155 = 555460 := by decide +kernel
private theorem value6 : evalPhi WheelTableA94.fast ps6 34751024 = 6665532 :=
  eval_delta WheelTableA94.fast ps5 13 34751024 2673155 7220992 555460 6665532
    (by decide) (by decide) rfl value5 cut6 rfl

private def ps7 : List ℕ := 17 :: ps6
private theorem row7 :
    ((List.range (17+1)).filter (fun n => decide n.Prime)).reverse = ps7 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 17 (by decide)]
  decide +kernel
private theorem agree7 : ∀ t, ps7.foldr advance id t = evalPhi WheelTableA94.fast ps7 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row7 agree6 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut7 : evalPhi WheelTableA94.fast ps6 2044177 = 392090 := by decide +kernel
private theorem value7 : evalPhi WheelTableA94.fast ps7 34751024 = 6273442 :=
  eval_delta WheelTableA94.fast ps6 17 34751024 2044177 6665532 392090 6273442
    (by decide) (by decide) rfl value6 cut7 rfl

private def ps8 : List ℕ := 19 :: ps7
private theorem row8 :
    ((List.range (19+1)).filter (fun n => decide n.Prime)).reverse = ps8 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 19 (by decide)]
  decide +kernel
private theorem agree8 : ∀ t, ps8.foldr advance id t = evalPhi WheelTableA94.fast ps8 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row8 agree7 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut8 : evalPhi WheelTableA94.fast ps7 1829001 = 330181 := by decide +kernel
private theorem value8 : evalPhi WheelTableA94.fast ps8 34751024 = 5943261 :=
  eval_delta WheelTableA94.fast ps7 19 34751024 1829001 6273442 330181 5943261
    (by decide) (by decide) rfl value7 cut8 rfl

private def ps9 : List ℕ := 23 :: ps8
private theorem row9 :
    ((List.range (23+1)).filter (fun n => decide n.Prime)).reverse = ps9 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 23 (by decide)]
  decide +kernel
private theorem agree9 : ∀ t, ps9.foldr advance id t = evalPhi WheelTableA94.fast ps9 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row9 agree8 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut9 : evalPhi WheelTableA94.fast ps8 1510914 = 258404 := by decide +kernel
private theorem value9 : evalPhi WheelTableA94.fast ps9 34751024 = 5684857 :=
  eval_delta WheelTableA94.fast ps8 23 34751024 1510914 5943261 258404 5684857
    (by decide) (by decide) rfl value8 cut9 rfl

private def ps10 : List ℕ := 29 :: ps9
private theorem row10 :
    ((List.range (29+1)).filter (fun n => decide n.Prime)).reverse = ps10 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 29 (by decide)]
  decide +kernel
private theorem agree10 : ∀ t, ps10.foldr advance id t = evalPhi WheelTableA94.fast ps10 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row10 agree9 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut10 : evalPhi WheelTableA94.fast ps9 1198311 = 196027 := by decide +kernel
private theorem value10 : evalPhi WheelTableA94.fast ps10 34751024 = 5488830 :=
  eval_delta WheelTableA94.fast ps9 29 34751024 1198311 5684857 196027 5488830
    (by decide) (by decide) rfl value9 cut10 rfl

private def ps11 : List ℕ := 31 :: ps10
private theorem row11 :
    ((List.range (31+1)).filter (fun n => decide n.Prime)).reverse = ps11 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 31 (by decide)]
  decide +kernel
private theorem agree11 : ∀ t, ps11.foldr advance id t = evalPhi WheelTableA94.fast ps11 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row11 agree10 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut11 : evalPhi WheelTableA94.fast ps10 1121000 = 177056 := by decide +kernel
private theorem value11 : evalPhi WheelTableA94.fast ps11 34751024 = 5311774 :=
  eval_delta WheelTableA94.fast ps10 31 34751024 1121000 5488830 177056 5311774
    (by decide) (by decide) rfl value10 cut11 rfl

private def ps12 : List ℕ := 37 :: ps11
private theorem row12 :
    ((List.range (37+1)).filter (fun n => decide n.Prime)).reverse = ps12 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 37 (by decide)]
  decide +kernel
private theorem agree12 : ∀ t, ps12.foldr advance id t = evalPhi WheelTableA94.fast ps12 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row12 agree11 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut12 : evalPhi WheelTableA94.fast ps11 939216 = 143554 := by decide +kernel
private theorem value12 : evalPhi WheelTableA94.fast ps12 34751024 = 5168220 :=
  eval_delta WheelTableA94.fast ps11 37 34751024 939216 5311774 143554 5168220
    (by decide) (by decide) rfl value11 cut12 rfl

private def ps13 : List ℕ := 41 :: ps12
private theorem row13 :
    ((List.range (41+1)).filter (fun n => decide n.Prime)).reverse = ps13 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 41 (by decide)]
  decide +kernel
private theorem agree13 : ∀ t, ps13.foldr advance id t = evalPhi WheelTableA94.fast ps13 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row13 agree12 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut13 : evalPhi WheelTableA94.fast ps12 847585 = 126039 := by decide +kernel
private theorem value13 : evalPhi WheelTableA94.fast ps13 34751024 = 5042181 :=
  eval_delta WheelTableA94.fast ps12 41 34751024 847585 5168220 126039 5042181
    (by decide) (by decide) rfl value12 cut13 rfl

private def ps14 : List ℕ := 43 :: ps13
private theorem row14 :
    ((List.range (43+1)).filter (fun n => decide n.Prime)).reverse = ps14 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 43 (by decide)]
  decide +kernel
private theorem agree14 : ∀ t, ps14.foldr advance id t = evalPhi WheelTableA94.fast ps14 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row14 agree13 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut14 : evalPhi WheelTableA94.fast ps13 808163 = 117267 := by decide +kernel
private theorem value14 : evalPhi WheelTableA94.fast ps14 34751024 = 4924914 :=
  eval_delta WheelTableA94.fast ps13 43 34751024 808163 5042181 117267 4924914
    (by decide) (by decide) rfl value13 cut14 rfl

private def ps15 : List ℕ := 47 :: ps14
private theorem row15 :
    ((List.range (47+1)).filter (fun n => decide n.Prime)).reverse = ps15 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 47 (by decide)]
  decide +kernel
private theorem agree15 : ∀ t, ps15.foldr advance id t = evalPhi WheelTableA94.fast ps15 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row15 agree14 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut15 : evalPhi WheelTableA94.fast ps14 739383 = 104818 := by decide +kernel
private theorem value15 : evalPhi WheelTableA94.fast ps15 34751024 = 4820096 :=
  eval_delta WheelTableA94.fast ps14 47 34751024 739383 4924914 104818 4820096
    (by decide) (by decide) rfl value14 cut15 rfl

private def ps16 : List ℕ := 53 :: ps15
private theorem row16 :
    ((List.range (53+1)).filter (fun n => decide n.Prime)).reverse = ps16 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 53 (by decide)]
  decide +kernel
private theorem agree16 : ∀ t, ps16.foldr advance id t = evalPhi WheelTableA94.fast ps16 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row16 agree15 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut16 : evalPhi WheelTableA94.fast ps15 655679 = 91011 := by decide +kernel
private theorem value16 : evalPhi WheelTableA94.fast ps16 34751024 = 4729085 :=
  eval_delta WheelTableA94.fast ps15 53 34751024 655679 4820096 91011 4729085
    (by decide) (by decide) rfl value15 cut16 rfl

private def ps17 : List ℕ := 59 :: ps16
private theorem row17 :
    ((List.range (59+1)).filter (fun n => decide n.Prime)).reverse = ps17 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 59 (by decide)]
  decide +kernel
private theorem agree17 : ∀ t, ps17.foldr advance id t = evalPhi WheelTableA94.fast ps17 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row17 agree16 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut17 : evalPhi WheelTableA94.fast ps16 589000 = 80263 := by decide +kernel
private theorem value17 : evalPhi WheelTableA94.fast ps17 34751024 = 4648822 :=
  eval_delta WheelTableA94.fast ps16 59 34751024 589000 4729085 80263 4648822
    (by decide) (by decide) rfl value16 cut17 rfl

private def ps18 : List ℕ := 61 :: ps17
private theorem row18 :
    ((List.range (61+1)).filter (fun n => decide n.Prime)).reverse = ps18 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 61 (by decide)]
  decide +kernel
private theorem agree18 : ∀ t, ps18.foldr advance id t = evalPhi WheelTableA94.fast ps18 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row18 agree17 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut18 : evalPhi WheelTableA94.fast ps17 569688 = 76347 := by decide +kernel
private theorem value18 : evalPhi WheelTableA94.fast ps18 34751024 = 4572475 :=
  eval_delta WheelTableA94.fast ps17 61 34751024 569688 4648822 76347 4572475
    (by decide) (by decide) rfl value17 cut18 rfl

private def ps19 : List ℕ := 67 :: ps18
private theorem row19 :
    ((List.range (67+1)).filter (fun n => decide n.Prime)).reverse = ps19 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 67 (by decide)]
  decide +kernel
private theorem agree19 : ∀ t, ps19.foldr advance id t = evalPhi WheelTableA94.fast ps19 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row19 agree18 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut19 : evalPhi WheelTableA94.fast ps18 518672 = 68415 := by decide +kernel
private theorem value19 : evalPhi WheelTableA94.fast ps19 34751024 = 4504060 :=
  eval_delta WheelTableA94.fast ps18 67 34751024 518672 4572475 68415 4504060
    (by decide) (by decide) rfl value18 cut19 rfl

private def ps20 : List ℕ := 71 :: ps19
private theorem row20 :
    ((List.range (71+1)).filter (fun n => decide n.Prime)).reverse = ps20 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 71 (by decide)]
  decide +kernel
private theorem agree20 : ∀ t, ps20.foldr advance id t = evalPhi WheelTableA94.fast ps20 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row20 agree19 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut20 : evalPhi WheelTableA94.fast ps19 489451 = 63625 := by decide +kernel
private theorem value20 : evalPhi WheelTableA94.fast ps20 34751024 = 4440435 :=
  eval_delta WheelTableA94.fast ps19 71 34751024 489451 4504060 63625 4440435
    (by decide) (by decide) rfl value19 cut20 rfl

private def ps21 : List ℕ := 73 :: ps20
private theorem row21 :
    ((List.range (73+1)).filter (fun n => decide n.Prime)).reverse = ps21 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 73 (by decide)]
  decide +kernel
private theorem agree21 : ∀ t, ps21.foldr advance id t = evalPhi WheelTableA94.fast ps21 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row21 agree20 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut21 : evalPhi WheelTableA94.fast ps20 476041 = 61021 := by decide +kernel
private theorem value21 : evalPhi WheelTableA94.fast ps21 34751024 = 4379414 :=
  eval_delta WheelTableA94.fast ps20 73 34751024 476041 4440435 61021 4379414
    (by decide) (by decide) rfl value20 cut21 rfl

private def ps22 : List ℕ := 79 :: ps21
private theorem row22 :
    ((List.range (79+1)).filter (fun n => decide n.Prime)).reverse = ps22 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 79 (by decide)]
  decide +kernel
private theorem agree22 : ∀ t, ps22.foldr advance id t = evalPhi WheelTableA94.fast ps22 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row22 agree21 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut22 : evalPhi WheelTableA94.fast ps21 439886 = 55621 := by decide +kernel
private theorem value22 : evalPhi WheelTableA94.fast ps22 34751024 = 4323793 :=
  eval_delta WheelTableA94.fast ps21 79 34751024 439886 4379414 55621 4323793
    (by decide) (by decide) rfl value21 cut22 rfl

private def ps23 : List ℕ := 83 :: ps22
private theorem row23 :
    ((List.range (83+1)).filter (fun n => decide n.Prime)).reverse = ps23 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 83 (by decide)]
  decide +kernel
private theorem agree23 : ∀ t, ps23.foldr advance id t = evalPhi WheelTableA94.fast ps23 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row23 agree22 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut23 : evalPhi WheelTableA94.fast ps22 418687 = 52250 := by decide +kernel
private theorem value23 : evalPhi WheelTableA94.fast ps23 34751024 = 4271543 :=
  eval_delta WheelTableA94.fast ps22 83 34751024 418687 4323793 52250 4271543
    (by decide) (by decide) rfl value22 cut23 rfl

private def ps24 : List ℕ := 89 :: ps23
private theorem row24 :
    ((List.range (89+1)).filter (fun n => decide n.Prime)).reverse = ps24 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 89 (by decide)]
  decide +kernel
private theorem agree24 : ∀ t, ps24.foldr advance id t = evalPhi WheelTableA94.fast ps24 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row24 agree23 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut24 : evalPhi WheelTableA94.fast ps23 390460 = 48104 := by decide +kernel
private theorem value24 : evalPhi WheelTableA94.fast ps24 34751024 = 4223439 :=
  eval_delta WheelTableA94.fast ps23 89 34751024 390460 4271543 48104 4223439
    (by decide) (by decide) rfl value23 cut24 rfl

private def ps25 : List ℕ := 97 :: ps24
private theorem row25 :
    ((List.range (97+1)).filter (fun n => decide n.Prime)).reverse = ps25 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 97 (by decide)]
  decide +kernel
private theorem agree25 : ∀ t, ps25.foldr advance id t = evalPhi WheelTableA94.fast ps25 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row25 agree24 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut25 : evalPhi WheelTableA94.fast ps24 358257 = 43584 := by decide +kernel
private theorem value25 : evalPhi WheelTableA94.fast ps25 34751024 = 4179855 :=
  eval_delta WheelTableA94.fast ps24 97 34751024 358257 4223439 43584 4179855
    (by decide) (by decide) rfl value24 cut25 rfl

private def ps26 : List ℕ := 101 :: ps25
private theorem row26 :
    ((List.range (101+1)).filter (fun n => decide n.Prime)).reverse = ps26 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 101 (by decide)]
  decide +kernel
private theorem agree26 : ∀ t, ps26.foldr advance id t = evalPhi WheelTableA94.fast ps26 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row26 agree25 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut26 : evalPhi WheelTableA94.fast ps25 344069 = 41368 := by decide +kernel
private theorem value26 : evalPhi WheelTableA94.fast ps26 34751024 = 4138487 :=
  eval_delta WheelTableA94.fast ps25 101 34751024 344069 4179855 41368 4138487
    (by decide) (by decide) rfl value25 cut26 rfl

private def ps27 : List ℕ := 103 :: ps26
private theorem row27 :
    ((List.range (103+1)).filter (fun n => decide n.Prime)).reverse = ps27 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 103 (by decide)]
  decide +kernel
private theorem agree27 : ∀ t, ps27.foldr advance id t = evalPhi WheelTableA94.fast ps27 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row27 agree26 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut27 : evalPhi WheelTableA94.fast ps26 337388 = 40116 := by decide +kernel
private theorem value27 : evalPhi WheelTableA94.fast ps27 34751024 = 4098371 :=
  eval_delta WheelTableA94.fast ps26 103 34751024 337388 4138487 40116 4098371
    (by decide) (by decide) rfl value26 cut27 rfl

private def ps28 : List ℕ := 107 :: ps27
private theorem row28 :
    ((List.range (107+1)).filter (fun n => decide n.Prime)).reverse = ps28 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 107 (by decide)]
  decide +kernel
private theorem agree28 : ∀ t, ps28.foldr advance id t = evalPhi WheelTableA94.fast ps28 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row28 agree27 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut28 : evalPhi WheelTableA94.fast ps27 324775 = 38182 := by decide +kernel
private theorem value28 : evalPhi WheelTableA94.fast ps28 34751024 = 4060189 :=
  eval_delta WheelTableA94.fast ps27 107 34751024 324775 4098371 38182 4060189
    (by decide) (by decide) rfl value27 cut28 rfl

private def ps29 : List ℕ := 109 :: ps28
private theorem row29 :
    ((List.range (109+1)).filter (fun n => decide n.Prime)).reverse = ps29 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 109 (by decide)]
  decide +kernel
private theorem agree29 : ∀ t, ps29.foldr advance id t = evalPhi WheelTableA94.fast ps29 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row29 agree28 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut29 : evalPhi WheelTableA94.fast ps28 318816 = 37070 := by decide +kernel
private theorem value29 : evalPhi WheelTableA94.fast ps29 34751024 = 4023119 :=
  eval_delta WheelTableA94.fast ps28 109 34751024 318816 4060189 37070 4023119
    (by decide) (by decide) rfl value28 cut29 rfl

private def ps30 : List ℕ := 113 :: ps29
private theorem row30 :
    ((List.range (113+1)).filter (fun n => decide n.Prime)).reverse = ps30 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 113 (by decide)]
  decide +kernel
private theorem agree30 : ∀ t, ps30.foldr advance id t = evalPhi WheelTableA94.fast ps30 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row30 agree29 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut30 : evalPhi WheelTableA94.fast ps29 307531 = 35356 := by decide +kernel
private theorem value30 : evalPhi WheelTableA94.fast ps30 34751024 = 3987763 :=
  eval_delta WheelTableA94.fast ps29 113 34751024 307531 4023119 35356 3987763
    (by decide) (by decide) rfl value29 cut30 rfl

private def ps31 : List ℕ := 127 :: ps30
private theorem row31 :
    ((List.range (127+1)).filter (fun n => decide n.Prime)).reverse = ps31 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 127 (by decide)]
  decide +kernel
private theorem agree31 : ∀ t, ps31.foldr advance id t = evalPhi WheelTableA94.fast ps31 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row31 agree30 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut31 : evalPhi WheelTableA94.fast ps30 273630 = 31086 := by decide +kernel
private theorem value31 : evalPhi WheelTableA94.fast ps31 34751024 = 3956677 :=
  eval_delta WheelTableA94.fast ps30 127 34751024 273630 3987763 31086 3956677
    (by decide) (by decide) rfl value30 cut31 rfl

private def ps32 : List ℕ := 131 :: ps31
private theorem row32 :
    ((List.range (131+1)).filter (fun n => decide n.Prime)).reverse = ps32 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 131 (by decide)]
  decide +kernel
private theorem agree32 : ∀ t, ps32.foldr advance id t = evalPhi WheelTableA94.fast ps32 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row32 agree31 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut32 : evalPhi WheelTableA94.fast ps31 265274 = 29829 := by decide +kernel
private theorem value32 : evalPhi WheelTableA94.fast ps32 34751024 = 3926848 :=
  eval_delta WheelTableA94.fast ps31 131 34751024 265274 3956677 29829 3926848
    (by decide) (by decide) rfl value31 cut32 rfl

private def ps33 : List ℕ := 137 :: ps32
private theorem row33 :
    ((List.range (137+1)).filter (fun n => decide n.Prime)).reverse = ps33 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 137 (by decide)]
  decide +kernel
private theorem agree33 : ∀ t, ps33.foldr advance id t = evalPhi WheelTableA94.fast ps33 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row33 agree32 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut33 : evalPhi WheelTableA94.fast ps32 253657 = 28240 := by decide +kernel
private theorem value33 : evalPhi WheelTableA94.fast ps33 34751024 = 3898608 :=
  eval_delta WheelTableA94.fast ps32 137 34751024 253657 3926848 28240 3898608
    (by decide) (by decide) rfl value32 cut33 rfl

private def ps34 : List ℕ := 139 :: ps33
private theorem row34 :
    ((List.range (139+1)).filter (fun n => decide n.Prime)).reverse = ps34 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 139 (by decide)]
  decide +kernel
private theorem agree34 : ∀ t, ps34.foldr advance id t = evalPhi WheelTableA94.fast ps34 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row34 agree33 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut34 : evalPhi WheelTableA94.fast ps33 250007 = 27586 := by decide +kernel
private theorem value34 : evalPhi WheelTableA94.fast ps34 34751024 = 3871022 :=
  eval_delta WheelTableA94.fast ps33 139 34751024 250007 3898608 27586 3871022
    (by decide) (by decide) rfl value33 cut34 rfl

private def ps35 : List ℕ := 149 :: ps34
private theorem row35 :
    ((List.range (149+1)).filter (fun n => decide n.Prime)).reverse = ps35 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 149 (by decide)]
  decide +kernel
private theorem agree35 : ∀ t, ps35.foldr advance id t = evalPhi WheelTableA94.fast ps35 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row35 agree34 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut35 : evalPhi WheelTableA94.fast ps34 233228 = 25465 := by decide +kernel
private theorem value35 : evalPhi WheelTableA94.fast ps35 34751024 = 3845557 :=
  eval_delta WheelTableA94.fast ps34 149 34751024 233228 3871022 25465 3845557
    (by decide) (by decide) rfl value34 cut35 rfl

private def ps36 : List ℕ := 151 :: ps35
private theorem row36 :
    ((List.range (151+1)).filter (fun n => decide n.Prime)).reverse = ps36 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 151 (by decide)]
  decide +kernel
private theorem agree36 : ∀ t, ps36.foldr advance id t = evalPhi WheelTableA94.fast ps36 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row36 agree35 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut36 : evalPhi WheelTableA94.fast ps35 230139 = 24918 := by decide +kernel
private theorem value36 : evalPhi WheelTableA94.fast ps36 34751024 = 3820639 :=
  eval_delta WheelTableA94.fast ps35 151 34751024 230139 3845557 24918 3820639
    (by decide) (by decide) rfl value35 cut36 rfl

private def ps37 : List ℕ := 157 :: ps36
private theorem row37 :
    ((List.range (157+1)).filter (fun n => decide n.Prime)).reverse = ps37 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 157 (by decide)]
  decide +kernel
private theorem agree37 : ∀ t, ps37.foldr advance id t = evalPhi WheelTableA94.fast ps37 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row37 agree36 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut37 : evalPhi WheelTableA94.fast ps36 221344 = 23744 := by decide +kernel
private theorem value37 : evalPhi WheelTableA94.fast ps37 34751024 = 3796895 :=
  eval_delta WheelTableA94.fast ps36 157 34751024 221344 3820639 23744 3796895
    (by decide) (by decide) rfl value36 cut37 rfl

private def ps38 : List ℕ := 163 :: ps37
private theorem row38 :
    ((List.range (163+1)).filter (fun n => decide n.Prime)).reverse = ps38 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 163 (by decide)]
  decide +kernel
private theorem agree38 : ∀ t, ps38.foldr advance id t = evalPhi WheelTableA94.fast ps38 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row38 agree37 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut38 : evalPhi WheelTableA94.fast ps37 213196 = 22676 := by decide +kernel
private theorem value38 : evalPhi WheelTableA94.fast ps38 34751024 = 3774219 :=
  eval_delta WheelTableA94.fast ps37 163 34751024 213196 3796895 22676 3774219
    (by decide) (by decide) rfl value37 cut38 rfl

private def ps39 : List ℕ := 167 :: ps38
private theorem row39 :
    ((List.range (167+1)).filter (fun n => decide n.Prime)).reverse = ps39 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 167 (by decide)]
  decide +kernel
private theorem agree39 : ∀ t, ps39.foldr advance id t = evalPhi WheelTableA94.fast ps39 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row39 agree38 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut39 : evalPhi WheelTableA94.fast ps38 208089 = 21947 := by decide +kernel
private theorem value39 : evalPhi WheelTableA94.fast ps39 34751024 = 3752272 :=
  eval_delta WheelTableA94.fast ps38 167 34751024 208089 3774219 21947 3752272
    (by decide) (by decide) rfl value38 cut39 rfl

private def ps40 : List ℕ := 173 :: ps39
private theorem row40 :
    ((List.range (173+1)).filter (fun n => decide n.Prime)).reverse = ps40 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 173 (by decide)]
  decide +kernel
private theorem agree40 : ∀ t, ps40.foldr advance id t = evalPhi WheelTableA94.fast ps40 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row40 agree39 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut40 : evalPhi WheelTableA94.fast ps39 200872 = 21013 := by decide +kernel
private theorem value40 : evalPhi WheelTableA94.fast ps40 34751024 = 3731259 :=
  eval_delta WheelTableA94.fast ps39 173 34751024 200872 3752272 21013 3731259
    (by decide) (by decide) rfl value39 cut40 rfl

private def ps41 : List ℕ := 179 :: ps40
private theorem row41 :
    ((List.range (179+1)).filter (fun n => decide n.Prime)).reverse = ps41 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 179 (by decide)]
  decide +kernel
private theorem agree41 : ∀ t, ps41.foldr advance id t = evalPhi WheelTableA94.fast ps41 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row41 agree40 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut41 : evalPhi WheelTableA94.fast ps40 194139 = 20149 := by decide +kernel
private theorem value41 : evalPhi WheelTableA94.fast ps41 34751024 = 3711110 :=
  eval_delta WheelTableA94.fast ps40 179 34751024 194139 3731259 20149 3711110
    (by decide) (by decide) rfl value40 cut41 rfl

private def ps42 : List ℕ := 181 :: ps41
private theorem row42 :
    ((List.range (181+1)).filter (fun n => decide n.Prime)).reverse = ps42 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 181 (by decide)]
  decide +kernel
private theorem agree42 : ∀ t, ps42.foldr advance id t = evalPhi WheelTableA94.fast ps42 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row42 agree41 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut42 : evalPhi WheelTableA94.fast ps41 191994 = 19774 := by decide +kernel
private theorem value42 : evalPhi WheelTableA94.fast ps42 34751024 = 3691336 :=
  eval_delta WheelTableA94.fast ps41 181 34751024 191994 3711110 19774 3691336
    (by decide) (by decide) rfl value41 cut42 rfl

private def ps43 : List ℕ := 191 :: ps42
private theorem row43 :
    ((List.range (191+1)).filter (fun n => decide n.Prime)).reverse = ps43 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 191 (by decide)]
  decide +kernel
private theorem agree43 : ∀ t, ps43.foldr advance id t = evalPhi WheelTableA94.fast ps43 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row43 agree42 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut43 : evalPhi WheelTableA94.fast ps42 181942 = 18584 := by decide +kernel
private theorem value43 : evalPhi WheelTableA94.fast ps43 34751024 = 3672752 :=
  eval_delta WheelTableA94.fast ps42 191 34751024 181942 3691336 18584 3672752
    (by decide) (by decide) rfl value42 cut43 rfl

private def ps44 : List ℕ := 193 :: ps43
private theorem row44 :
    ((List.range (193+1)).filter (fun n => decide n.Prime)).reverse = ps44 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 193 (by decide)]
  decide +kernel
private theorem agree44 : ∀ t, ps44.foldr advance id t = evalPhi WheelTableA94.fast ps44 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row44 agree43 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut44 : evalPhi WheelTableA94.fast ps43 180057 = 18279 := by decide +kernel
private theorem value44 : evalPhi WheelTableA94.fast ps44 34751024 = 3654473 :=
  eval_delta WheelTableA94.fast ps43 193 34751024 180057 3672752 18279 3654473
    (by decide) (by decide) rfl value43 cut44 rfl

private def ps45 : List ℕ := 197 :: ps44
private theorem row45 :
    ((List.range (197+1)).filter (fun n => decide n.Prime)).reverse = ps45 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 197 (by decide)]
  decide +kernel
private theorem agree45 : ∀ t, ps45.foldr advance id t = evalPhi WheelTableA94.fast ps45 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row45 agree44 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut45 : evalPhi WheelTableA94.fast ps44 176401 = 17786 := by decide +kernel
private theorem value45 : evalPhi WheelTableA94.fast ps45 34751024 = 3636687 :=
  eval_delta WheelTableA94.fast ps44 197 34751024 176401 3654473 17786 3636687
    (by decide) (by decide) rfl value44 cut45 rfl

private def ps46 : List ℕ := 199 :: ps45
private theorem row46 :
    ((List.range (199+1)).filter (fun n => decide n.Prime)).reverse = ps46 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 199 (by decide)]
  decide +kernel
private theorem agree46 : ∀ t, ps46.foldr advance id t = evalPhi WheelTableA94.fast ps46 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row46 agree45 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut46 : evalPhi WheelTableA94.fast ps45 174628 = 17491 := by decide +kernel
private theorem value46 : evalPhi WheelTableA94.fast ps46 34751024 = 3619196 :=
  eval_delta WheelTableA94.fast ps45 199 34751024 174628 3636687 17491 3619196
    (by decide) (by decide) rfl value45 cut46 rfl

private def ps47 : List ℕ := 211 :: ps46
private theorem row47 :
    ((List.range (211+1)).filter (fun n => decide n.Prime)).reverse = ps47 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 211 (by decide)]
  decide +kernel
private theorem agree47 : ∀ t, ps47.foldr advance id t = evalPhi WheelTableA94.fast ps47 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row47 agree46 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut47 : evalPhi WheelTableA94.fast ps46 164696 = 16392 := by decide +kernel
private theorem value47 : evalPhi WheelTableA94.fast ps47 34751024 = 3602804 :=
  eval_delta WheelTableA94.fast ps46 211 34751024 164696 3619196 16392 3602804
    (by decide) (by decide) rfl value46 cut47 rfl

private def ps48 : List ℕ := 223 :: ps47
private theorem row48 :
    ((List.range (223+1)).filter (fun n => decide n.Prime)).reverse = ps48 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 223 (by decide)]
  decide +kernel
private theorem agree48 : ∀ t, ps48.foldr advance id t = evalPhi WheelTableA94.fast ps48 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row48 agree47 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut48 : evalPhi WheelTableA94.fast ps47 155834 = 15431 := by decide +kernel
private theorem value48 : evalPhi WheelTableA94.fast ps48 34751024 = 3587373 :=
  eval_delta WheelTableA94.fast ps47 223 34751024 155834 3602804 15431 3587373
    (by decide) (by decide) rfl value47 cut48 rfl

private def ps49 : List ℕ := 227 :: ps48
private theorem row49 :
    ((List.range (227+1)).filter (fun n => decide n.Prime)).reverse = ps49 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 227 (by decide)]
  decide +kernel
private theorem agree49 : ∀ t, ps49.foldr advance id t = evalPhi WheelTableA94.fast ps49 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row49 agree48 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut49 : evalPhi WheelTableA94.fast ps48 153088 = 15072 := by decide +kernel
private theorem value49 : evalPhi WheelTableA94.fast ps49 34751024 = 3572301 :=
  eval_delta WheelTableA94.fast ps48 227 34751024 153088 3587373 15072 3572301
    (by decide) (by decide) rfl value48 cut49 rfl

private def ps50 : List ℕ := 229 :: ps49
private theorem row50 :
    ((List.range (229+1)).filter (fun n => decide n.Prime)).reverse = ps50 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 229 (by decide)]
  decide +kernel
private theorem agree50 : ∀ t, ps50.foldr advance id t = evalPhi WheelTableA94.fast ps50 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row50 agree49 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut50 : evalPhi WheelTableA94.fast ps49 151751 = 14865 := by decide +kernel
private theorem value50 : evalPhi WheelTableA94.fast ps50 34751024 = 3557436 :=
  eval_delta WheelTableA94.fast ps49 229 34751024 151751 3572301 14865 3557436
    (by decide) (by decide) rfl value49 cut50 rfl

private def ps51 : List ℕ := 233 :: ps50
private theorem row51 :
    ((List.range (233+1)).filter (fun n => decide n.Prime)).reverse = ps51 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 233 (by decide)]
  decide +kernel
private theorem agree51 : ∀ t, ps51.foldr advance id t = evalPhi WheelTableA94.fast ps51 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row51 agree50 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut51 : evalPhi WheelTableA94.fast ps50 149146 = 14529 := by decide +kernel
private theorem value51 : evalPhi WheelTableA94.fast ps51 34751024 = 3542907 :=
  eval_delta WheelTableA94.fast ps50 233 34751024 149146 3557436 14529 3542907
    (by decide) (by decide) rfl value50 cut51 rfl

private def ps52 : List ℕ := 239 :: ps51
private theorem row52 :
    ((List.range (239+1)).filter (fun n => decide n.Prime)).reverse = ps52 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 239 (by decide)]
  decide +kernel
private theorem agree52 : ∀ t, ps52.foldr advance id t = evalPhi WheelTableA94.fast ps52 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row52 agree51 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut52 : evalPhi WheelTableA94.fast ps51 145401 = 14096 := by decide +kernel
private theorem value52 : evalPhi WheelTableA94.fast ps52 34751024 = 3528811 :=
  eval_delta WheelTableA94.fast ps51 239 34751024 145401 3542907 14096 3528811
    (by decide) (by decide) rfl value51 cut52 rfl

private def ps53 : List ℕ := 241 :: ps52
private theorem row53 :
    ((List.range (241+1)).filter (fun n => decide n.Prime)).reverse = ps53 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 241 (by decide)]
  decide +kernel
private theorem agree53 : ∀ t, ps53.foldr advance id t = evalPhi WheelTableA94.fast ps53 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row53 agree52 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut53 : evalPhi WheelTableA94.fast ps52 144195 = 13923 := by decide +kernel
private theorem value53 : evalPhi WheelTableA94.fast ps53 34751024 = 3514888 :=
  eval_delta WheelTableA94.fast ps52 241 34751024 144195 3528811 13923 3514888
    (by decide) (by decide) rfl value52 cut53 rfl

private def ps54 : List ℕ := 251 :: ps53
private theorem row54 :
    ((List.range (251+1)).filter (fun n => decide n.Prime)).reverse = ps54 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 251 (by decide)]
  decide +kernel
private theorem agree54 : ∀ t, ps54.foldr advance id t = evalPhi WheelTableA94.fast ps54 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row54 agree53 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut54 : evalPhi WheelTableA94.fast ps53 138450 = 13328 := by decide +kernel
private theorem value54 : evalPhi WheelTableA94.fast ps54 34751024 = 3501560 :=
  eval_delta WheelTableA94.fast ps53 251 34751024 138450 3514888 13328 3501560
    (by decide) (by decide) rfl value53 cut54 rfl

private def ps55 : List ℕ := 257 :: ps54
private theorem row55 :
    ((List.range (257+1)).filter (fun n => decide n.Prime)).reverse = ps55 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 257 (by decide)]
  decide +kernel
private theorem agree55 : ∀ t, ps55.foldr advance id t = evalPhi WheelTableA94.fast ps55 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row55 agree54 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut55 : evalPhi WheelTableA94.fast ps54 135217 = 12963 := by decide +kernel
private theorem value55 : evalPhi WheelTableA94.fast ps55 34751024 = 3488597 :=
  eval_delta WheelTableA94.fast ps54 257 34751024 135217 3501560 12963 3488597
    (by decide) (by decide) rfl value54 cut55 rfl

private def ps56 : List ℕ := 263 :: ps55
private theorem row56 :
    ((List.range (263+1)).filter (fun n => decide n.Prime)).reverse = ps56 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 263 (by decide)]
  decide +kernel
private theorem agree56 : ∀ t, ps56.foldr advance id t = evalPhi WheelTableA94.fast ps56 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row56 agree55 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut56 : evalPhi WheelTableA94.fast ps55 132133 = 12629 := by decide +kernel
private theorem value56 : evalPhi WheelTableA94.fast ps56 34751024 = 3475968 :=
  eval_delta WheelTableA94.fast ps55 263 34751024 132133 3488597 12629 3475968
    (by decide) (by decide) rfl value55 cut56 rfl

private def ps57 : List ℕ := 269 :: ps56
private theorem row57 :
    ((List.range (269+1)).filter (fun n => decide n.Prime)).reverse = ps57 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 269 (by decide)]
  decide +kernel
private theorem agree57 : ∀ t, ps57.foldr advance id t = evalPhi WheelTableA94.fast ps57 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row57 agree56 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut57 : evalPhi WheelTableA94.fast ps56 129185 = 12315 := by decide +kernel
private theorem value57 : evalPhi WheelTableA94.fast ps57 34751024 = 3463653 :=
  eval_delta WheelTableA94.fast ps56 269 34751024 129185 3475968 12315 3463653
    (by decide) (by decide) rfl value56 cut57 rfl

private def ps58 : List ℕ := 271 :: ps57
private theorem row58 :
    ((List.range (271+1)).filter (fun n => decide n.Prime)).reverse = ps58 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 271 (by decide)]
  decide +kernel
private theorem agree58 : ∀ t, ps58.foldr advance id t = evalPhi WheelTableA94.fast ps58 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row58 agree57 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut58 : evalPhi WheelTableA94.fast ps57 128232 = 12185 := by decide +kernel
private theorem value58 : evalPhi WheelTableA94.fast ps58 34751024 = 3451468 :=
  eval_delta WheelTableA94.fast ps57 271 34751024 128232 3463653 12185 3451468
    (by decide) (by decide) rfl value57 cut58 rfl

private def ps59 : List ℕ := 277 :: ps58
private theorem row59 :
    ((List.range (277+1)).filter (fun n => decide n.Prime)).reverse = ps59 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 277 (by decide)]
  decide +kernel
private theorem agree59 : ∀ t, ps59.foldr advance id t = evalPhi WheelTableA94.fast ps59 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row59 agree58 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut59 : evalPhi WheelTableA94.fast ps58 125454 = 11902 := by decide +kernel
private theorem value59 : evalPhi WheelTableA94.fast ps59 34751024 = 3439566 :=
  eval_delta WheelTableA94.fast ps58 277 34751024 125454 3451468 11902 3439566
    (by decide) (by decide) rfl value58 cut59 rfl

private def ps60 : List ℕ := 281 :: ps59
private theorem row60 :
    ((List.range (281+1)).filter (fun n => decide n.Prime)).reverse = ps60 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 281 (by decide)]
  decide +kernel
private theorem agree60 : ∀ t, ps60.foldr advance id t = evalPhi WheelTableA94.fast ps60 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row60 agree59 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut60 : evalPhi WheelTableA94.fast ps59 123669 = 11710 := by decide +kernel
private theorem value60 : evalPhi WheelTableA94.fast ps60 34751024 = 3427856 :=
  eval_delta WheelTableA94.fast ps59 281 34751024 123669 3439566 11710 3427856
    (by decide) (by decide) rfl value59 cut60 rfl

private def ps61 : List ℕ := 283 :: ps60
private theorem row61 :
    ((List.range (283+1)).filter (fun n => decide n.Prime)).reverse = ps61 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 283 (by decide)]
  decide +kernel
private theorem agree61 : ∀ t, ps61.foldr advance id t = evalPhi WheelTableA94.fast ps61 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row61 agree60 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut61 : evalPhi WheelTableA94.fast ps60 122795 = 11601 := by decide +kernel
private theorem value61 : evalPhi WheelTableA94.fast ps61 34751024 = 3416255 :=
  eval_delta WheelTableA94.fast ps60 283 34751024 122795 3427856 11601 3416255
    (by decide) (by decide) rfl value60 cut61 rfl

private def ps62 : List ℕ := 293 :: ps61
private theorem row62 :
    ((List.range (293+1)).filter (fun n => decide n.Prime)).reverse = ps62 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 293 (by decide)]
  decide +kernel
private theorem agree62 : ∀ t, ps62.foldr advance id t = evalPhi WheelTableA94.fast ps62 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row62 agree61 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut62 : evalPhi WheelTableA94.fast ps61 118604 = 11192 := by decide +kernel
private theorem value62 : evalPhi WheelTableA94.fast ps62 34751024 = 3405063 :=
  eval_delta WheelTableA94.fast ps61 293 34751024 118604 3416255 11192 3405063
    (by decide) (by decide) rfl value61 cut62 rfl

private def ps63 : List ℕ := 307 :: ps62
private theorem row63 :
    ((List.range (307+1)).filter (fun n => decide n.Prime)).reverse = ps63 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 307 (by decide)]
  decide +kernel
private theorem agree63 : ∀ t, ps63.foldr advance id t = evalPhi WheelTableA94.fast ps63 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row63 agree62 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut63 : evalPhi WheelTableA94.fast ps62 113195 = 10704 := by decide +kernel
private theorem value63 : evalPhi WheelTableA94.fast ps63 34751024 = 3394359 :=
  eval_delta WheelTableA94.fast ps62 307 34751024 113195 3405063 10704 3394359
    (by decide) (by decide) rfl value62 cut63 rfl

private def ps64 : List ℕ := 311 :: ps63
private theorem row64 :
    ((List.range (311+1)).filter (fun n => decide n.Prime)).reverse = ps64 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 311 (by decide)]
  decide +kernel
private theorem agree64 : ∀ t, ps64.foldr advance id t = evalPhi WheelTableA94.fast ps64 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row64 agree63 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut64 : evalPhi WheelTableA94.fast ps63 111739 = 10556 := by decide +kernel
private theorem value64 : evalPhi WheelTableA94.fast ps64 34751024 = 3383803 :=
  eval_delta WheelTableA94.fast ps63 311 34751024 111739 3394359 10556 3383803
    (by decide) (by decide) rfl value63 cut64 rfl

private def ps65 : List ℕ := 313 :: ps64
private theorem row65 :
    ((List.range (313+1)).filter (fun n => decide n.Prime)).reverse = ps65 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 313 (by decide)]
  decide +kernel
private theorem agree65 : ∀ t, ps65.foldr advance id t = evalPhi WheelTableA94.fast ps65 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row65 agree64 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut65 : evalPhi WheelTableA94.fast ps64 111025 = 10486 := by decide +kernel
private theorem value65 : evalPhi WheelTableA94.fast ps65 34751024 = 3373317 :=
  eval_delta WheelTableA94.fast ps64 313 34751024 111025 3383803 10486 3373317
    (by decide) (by decide) rfl value64 cut65 rfl

private def ps66 : List ℕ := 317 :: ps65
private theorem row66 :
    ((List.range (317+1)).filter (fun n => decide n.Prime)).reverse = ps66 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 317 (by decide)]
  decide +kernel
private theorem agree66 : ∀ t, ps66.foldr advance id t = evalPhi WheelTableA94.fast ps66 t :=
  refine_row WheelTableA94.fast WheelTableA94.fast_correct _ row66 agree65 (by decide) (by decide)
set_option maxRecDepth 7000 in
set_option maxHeartbeats 4000000 in
private theorem cut66 : evalPhi WheelTableA94.fast ps65 109624 = 10363 := by decide +kernel
private theorem value66 : evalPhi WheelTableA94.fast ps66 34751024 = 3362954 :=
  eval_delta WheelTableA94.fast ps65 317 34751024 109624 3373317 10363 3362954
    (by decide) (by decide) rfl value65 cut66 rfl

private theorem last_row :
    ((List.range (326+1)).filter (fun n => decide n.Prime)).reverse = ps66 := by
  rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct 326 (by decide)]
  decide +kernel

private theorem left_part :
    (((List.range (326+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id 34751024) +
       (Nat.primesLE 326).card = 3363020 := by
  rw [last_row,agree66,value66,Nat.primesLE_card_eq_primeCounting,←WheelTableA94.fast_correct 326 (by decide)]
  decide +kernel

private def term (p : ℕ) : ℕ := if 326<p then WheelTableA94.fast (34751024/p) - WheelTableA94.fast (p-1) else 0

private def rr0_184 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181]
set_option maxRecDepth 3000 in
private theorem okrr0_184 : (List.range' 0 184).filter (primeBit WheelTableA94.fast) = rr0_184 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr0_184 : (rr0_184.map term).sum = 0 := by decide +kernel

private def rr184_368 : List ℕ := [191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367]
set_option maxRecDepth 3000 in
private theorem okrr184_368 : (List.range' 184 184).filter (primeBit WheelTableA94.fast) = rr184_368 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr184_368 : (rr184_368.map term).sum = 66462 := by decide +kernel

private def rr0_368 : List ℕ := rr0_184 ++ rr184_368
set_option maxRecDepth 3000 in
private theorem okrr0_368 : (List.range' 0 368).filter (primeBit WheelTableA94.fast) = rr0_368 := merge_filter (primeBit WheelTableA94.fast) 0 184 184 rr0_184 rr184_368 okrr0_184 okrr184_368
set_option maxRecDepth 3000 in
private theorem vrr0_368 : (rr0_368.map term).sum = 66462 := by rw [rr0_368,List.map_append,List.sum_append,vrr0_184,vrr184_368]

private def rr368_552 : List ℕ := [373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547]
set_option maxRecDepth 3000 in
private theorem okrr368_552 : (List.range' 368 184).filter (primeBit WheelTableA94.fast) = rr368_552 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr368_552 : (rr368_552.map term).sum = 210577 := by decide +kernel

private def rr552_736 : List ℕ := [557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733]
set_option maxRecDepth 3000 in
private theorem okrr552_736 : (List.range' 552 184).filter (primeBit WheelTableA94.fast) = rr552_736 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr552_736 : (rr552_736.map term).sum = 158207 := by decide +kernel

private def rr368_736 : List ℕ := rr368_552 ++ rr552_736
set_option maxRecDepth 3000 in
private theorem okrr368_736 : (List.range' 368 368).filter (primeBit WheelTableA94.fast) = rr368_736 := merge_filter (primeBit WheelTableA94.fast) 368 184 184 rr368_552 rr552_736 okrr368_552 okrr552_736
set_option maxRecDepth 3000 in
private theorem vrr368_736 : (rr368_736.map term).sum = 368784 := by rw [rr368_736,List.map_append,List.sum_append,vrr368_552,vrr552_736]

private def rr0_736 : List ℕ := rr0_368 ++ rr368_736
set_option maxRecDepth 3000 in
private theorem okrr0_736 : (List.range' 0 736).filter (primeBit WheelTableA94.fast) = rr0_736 := merge_filter (primeBit WheelTableA94.fast) 0 368 368 rr0_368 rr368_736 okrr0_368 okrr368_736
set_option maxRecDepth 3000 in
private theorem vrr0_736 : (rr0_736.map term).sum = 435246 := by rw [rr0_736,List.map_append,List.sum_append,vrr0_368,vrr368_736]

private def rr736_920 : List ℕ := [739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919]
set_option maxRecDepth 3000 in
private theorem okrr736_920 : (List.range' 736 184).filter (primeBit WheelTableA94.fast) = rr736_920 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr736_920 : (rr736_920.map term).sum = 115150 := by decide +kernel

private def rr920_1104 : List ℕ := [929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103]
set_option maxRecDepth 3000 in
private theorem okrr920_1104 : (List.range' 920 184).filter (primeBit WheelTableA94.fast) = rr920_1104 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr920_1104 : (rr920_1104.map term).sum = 97508 := by decide +kernel

private def rr736_1104 : List ℕ := rr736_920 ++ rr920_1104
set_option maxRecDepth 3000 in
private theorem okrr736_1104 : (List.range' 736 368).filter (primeBit WheelTableA94.fast) = rr736_1104 := merge_filter (primeBit WheelTableA94.fast) 736 184 184 rr736_920 rr920_1104 okrr736_920 okrr920_1104
set_option maxRecDepth 3000 in
private theorem vrr736_1104 : (rr736_1104.map term).sum = 212658 := by rw [rr736_1104,List.map_append,List.sum_append,vrr736_920,vrr920_1104]

private def rr1104_1288 : List ℕ := [1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283]
set_option maxRecDepth 3000 in
private theorem okrr1104_1288 : (List.range' 1104 184).filter (primeBit WheelTableA94.fast) = rr1104_1288 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1104_1288 : (rr1104_1288.map term).sum = 68062 := by decide +kernel

private def rr1288_1473 : List ℕ := [1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471]
set_option maxRecDepth 3000 in
private theorem okrr1288_1473 : (List.range' 1288 185).filter (primeBit WheelTableA94.fast) = rr1288_1473 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1288_1473 : (rr1288_1473.map term).sum = 64208 := by decide +kernel

private def rr1104_1473 : List ℕ := rr1104_1288 ++ rr1288_1473
set_option maxRecDepth 3000 in
private theorem okrr1104_1473 : (List.range' 1104 369).filter (primeBit WheelTableA94.fast) = rr1104_1473 := merge_filter (primeBit WheelTableA94.fast) 1104 184 185 rr1104_1288 rr1288_1473 okrr1104_1288 okrr1288_1473
set_option maxRecDepth 3000 in
private theorem vrr1104_1473 : (rr1104_1473.map term).sum = 132270 := by rw [rr1104_1473,List.map_append,List.sum_append,vrr1104_1288,vrr1288_1473]

private def rr736_1473 : List ℕ := rr736_1104 ++ rr1104_1473
set_option maxRecDepth 3000 in
private theorem okrr736_1473 : (List.range' 736 737).filter (primeBit WheelTableA94.fast) = rr736_1473 := merge_filter (primeBit WheelTableA94.fast) 736 368 369 rr736_1104 rr1104_1473 okrr736_1104 okrr1104_1473
set_option maxRecDepth 3000 in
private theorem vrr736_1473 : (rr736_1473.map term).sum = 344928 := by rw [rr736_1473,List.map_append,List.sum_append,vrr736_1104,vrr1104_1473]

private def rr0_1473 : List ℕ := rr0_736 ++ rr736_1473
set_option maxRecDepth 3000 in
private theorem okrr0_1473 : (List.range' 0 1473).filter (primeBit WheelTableA94.fast) = rr0_1473 := merge_filter (primeBit WheelTableA94.fast) 0 736 737 rr0_736 rr736_1473 okrr0_736 okrr736_1473
set_option maxRecDepth 3000 in
private theorem vrr0_1473 : (rr0_1473.map term).sum = 780174 := by rw [rr0_1473,List.map_append,List.sum_append,vrr0_736,vrr736_1473]

private def rr1473_1657 : List ℕ := [1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637]
set_option maxRecDepth 3000 in
private theorem okrr1473_1657 : (List.range' 1473 184).filter (primeBit WheelTableA94.fast) = rr1473_1657 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1473_1657 : (rr1473_1657.map term).sum = 58533 := by decide +kernel

private def rr1657_1841 : List ℕ := [1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831]
set_option maxRecDepth 3000 in
private theorem okrr1657_1841 : (List.range' 1657 184).filter (primeBit WheelTableA94.fast) = rr1657_1841 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1657_1841 : (rr1657_1841.map term).sum = 45754 := by decide +kernel

private def rr1473_1841 : List ℕ := rr1473_1657 ++ rr1657_1841
set_option maxRecDepth 3000 in
private theorem okrr1473_1841 : (List.range' 1473 368).filter (primeBit WheelTableA94.fast) = rr1473_1841 := merge_filter (primeBit WheelTableA94.fast) 1473 184 184 rr1473_1657 rr1657_1841 okrr1473_1657 okrr1657_1841
set_option maxRecDepth 3000 in
private theorem vrr1473_1841 : (rr1473_1841.map term).sum = 104287 := by rw [rr1473_1841,List.map_append,List.sum_append,vrr1473_1657,vrr1657_1841]

private def rr1841_2025 : List ℕ := [1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017]
set_option maxRecDepth 3000 in
private theorem okrr1841_2025 : (List.range' 1841 184).filter (primeBit WheelTableA94.fast) = rr1841_2025 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr1841_2025 : (rr1841_2025.map term).sum = 42452 := by decide +kernel

private def rr2025_2210 : List ℕ := [2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207]
set_option maxRecDepth 3000 in
private theorem okrr2025_2210 : (List.range' 2025 185).filter (primeBit WheelTableA94.fast) = rr2025_2210 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2025_2210 : (rr2025_2210.map term).sum = 36625 := by decide +kernel

private def rr1841_2210 : List ℕ := rr1841_2025 ++ rr2025_2210
set_option maxRecDepth 3000 in
private theorem okrr1841_2210 : (List.range' 1841 369).filter (primeBit WheelTableA94.fast) = rr1841_2210 := merge_filter (primeBit WheelTableA94.fast) 1841 184 185 rr1841_2025 rr2025_2210 okrr1841_2025 okrr2025_2210
set_option maxRecDepth 3000 in
private theorem vrr1841_2210 : (rr1841_2210.map term).sum = 79077 := by rw [rr1841_2210,List.map_append,List.sum_append,vrr1841_2025,vrr2025_2210]

private def rr1473_2210 : List ℕ := rr1473_1841 ++ rr1841_2210
set_option maxRecDepth 3000 in
private theorem okrr1473_2210 : (List.range' 1473 737).filter (primeBit WheelTableA94.fast) = rr1473_2210 := merge_filter (primeBit WheelTableA94.fast) 1473 368 369 rr1473_1841 rr1841_2210 okrr1473_1841 okrr1841_2210
set_option maxRecDepth 3000 in
private theorem vrr1473_2210 : (rr1473_2210.map term).sum = 183364 := by rw [rr1473_2210,List.map_append,List.sum_append,vrr1473_1841,vrr1841_2210]

private def rr2210_2394 : List ℕ := [2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393]
set_option maxRecDepth 3000 in
private theorem okrr2210_2394 : (List.range' 2210 184).filter (primeBit WheelTableA94.fast) = rr2210_2394 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2210_2394 : (rr2210_2394.map term).sum = 38285 := by decide +kernel

private def rr2394_2578 : List ℕ := [2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557]
set_option maxRecDepth 3000 in
private theorem okrr2394_2578 : (List.range' 2394 184).filter (primeBit WheelTableA94.fast) = rr2394_2578 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2394_2578 : (rr2394_2578.map term).sum = 24423 := by decide +kernel

private def rr2210_2578 : List ℕ := rr2210_2394 ++ rr2394_2578
set_option maxRecDepth 3000 in
private theorem okrr2210_2578 : (List.range' 2210 368).filter (primeBit WheelTableA94.fast) = rr2210_2578 := merge_filter (primeBit WheelTableA94.fast) 2210 184 184 rr2210_2394 rr2394_2578 okrr2210_2394 okrr2394_2578
set_option maxRecDepth 3000 in
private theorem vrr2210_2578 : (rr2210_2578.map term).sum = 62708 := by rw [rr2210_2578,List.map_append,List.sum_append,vrr2210_2394,vrr2394_2578]

private def rr2578_2762 : List ℕ := [2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753]
set_option maxRecDepth 3000 in
private theorem okrr2578_2762 : (List.range' 2578 184).filter (primeBit WheelTableA94.fast) = rr2578_2762 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2578_2762 : (rr2578_2762.map term).sum = 31294 := by decide +kernel

private def rr2762_2947 : List ℕ := [2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939]
set_option maxRecDepth 3000 in
private theorem okrr2762_2947 : (List.range' 2762 185).filter (primeBit WheelTableA94.fast) = rr2762_2947 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2762_2947 : (rr2762_2947.map term).sum = 23019 := by decide +kernel

private def rr2578_2947 : List ℕ := rr2578_2762 ++ rr2762_2947
set_option maxRecDepth 3000 in
private theorem okrr2578_2947 : (List.range' 2578 369).filter (primeBit WheelTableA94.fast) = rr2578_2947 := merge_filter (primeBit WheelTableA94.fast) 2578 184 185 rr2578_2762 rr2762_2947 okrr2578_2762 okrr2762_2947
set_option maxRecDepth 3000 in
private theorem vrr2578_2947 : (rr2578_2947.map term).sum = 54313 := by rw [rr2578_2947,List.map_append,List.sum_append,vrr2578_2762,vrr2762_2947]

private def rr2210_2947 : List ℕ := rr2210_2578 ++ rr2578_2947
set_option maxRecDepth 3000 in
private theorem okrr2210_2947 : (List.range' 2210 737).filter (primeBit WheelTableA94.fast) = rr2210_2947 := merge_filter (primeBit WheelTableA94.fast) 2210 368 369 rr2210_2578 rr2578_2947 okrr2210_2578 okrr2578_2947
set_option maxRecDepth 3000 in
private theorem vrr2210_2947 : (rr2210_2947.map term).sum = 117021 := by rw [rr2210_2947,List.map_append,List.sum_append,vrr2210_2578,vrr2578_2947]

private def rr1473_2947 : List ℕ := rr1473_2210 ++ rr2210_2947
set_option maxRecDepth 3000 in
private theorem okrr1473_2947 : (List.range' 1473 1474).filter (primeBit WheelTableA94.fast) = rr1473_2947 := merge_filter (primeBit WheelTableA94.fast) 1473 737 737 rr1473_2210 rr2210_2947 okrr1473_2210 okrr2210_2947
set_option maxRecDepth 3000 in
private theorem vrr1473_2947 : (rr1473_2947.map term).sum = 300385 := by rw [rr1473_2947,List.map_append,List.sum_append,vrr1473_2210,vrr2210_2947]

private def rr0_2947 : List ℕ := rr0_1473 ++ rr1473_2947
set_option maxRecDepth 3000 in
private theorem okrr0_2947 : (List.range' 0 2947).filter (primeBit WheelTableA94.fast) = rr0_2947 := merge_filter (primeBit WheelTableA94.fast) 0 1473 1474 rr0_1473 rr1473_2947 okrr0_1473 okrr1473_2947
set_option maxRecDepth 3000 in
private theorem vrr0_2947 : (rr0_2947.map term).sum = 1080559 := by rw [rr0_2947,List.map_append,List.sum_append,vrr0_1473,vrr1473_2947]

private def rr2947_3131 : List ℕ := [2953,2957,2963,2969,2971,2999,3001,3011,3019,3023,3037,3041,3049,3061,3067,3079,3083,3089,3109,3119,3121]
set_option maxRecDepth 3000 in
private theorem okrr2947_3131 : (List.range' 2947 184).filter (primeBit WheelTableA94.fast) = rr2947_3131 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr2947_3131 : (rr2947_3131.map term).sum = 19881 := by decide +kernel

private def rr3131_3315 : List ℕ := [3137,3163,3167,3169,3181,3187,3191,3203,3209,3217,3221,3229,3251,3253,3257,3259,3271,3299,3301,3307,3313]
set_option maxRecDepth 3000 in
private theorem okrr3131_3315 : (List.range' 3131 184).filter (primeBit WheelTableA94.fast) = rr3131_3315 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3131_3315 : (rr3131_3315.map term).sum = 17976 := by decide +kernel

private def rr2947_3315 : List ℕ := rr2947_3131 ++ rr3131_3315
set_option maxRecDepth 3000 in
private theorem okrr2947_3315 : (List.range' 2947 368).filter (primeBit WheelTableA94.fast) = rr2947_3315 := merge_filter (primeBit WheelTableA94.fast) 2947 184 184 rr2947_3131 rr3131_3315 okrr2947_3131 okrr3131_3315
set_option maxRecDepth 3000 in
private theorem vrr2947_3315 : (rr2947_3315.map term).sum = 37857 := by rw [rr2947_3315,List.map_append,List.sum_append,vrr2947_3131,vrr3131_3315]

private def rr3315_3499 : List ℕ := [3319,3323,3329,3331,3343,3347,3359,3361,3371,3373,3389,3391,3407,3413,3433,3449,3457,3461,3463,3467,3469,3491]
set_option maxRecDepth 3000 in
private theorem okrr3315_3499 : (List.range' 3315 184).filter (primeBit WheelTableA94.fast) = rr3315_3499 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3315_3499 : (rr3315_3499.map term).sum = 17121 := by decide +kernel

private def rr3499_3684 : List ℕ := [3499,3511,3517,3527,3529,3533,3539,3541,3547,3557,3559,3571,3581,3583,3593,3607,3613,3617,3623,3631,3637,3643,3659,3671,3673,3677]
set_option maxRecDepth 3000 in
private theorem okrr3499_3684 : (List.range' 3499 185).filter (primeBit WheelTableA94.fast) = rr3499_3684 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3499_3684 : (rr3499_3684.map term).sum = 18097 := by decide +kernel

private def rr3315_3684 : List ℕ := rr3315_3499 ++ rr3499_3684
set_option maxRecDepth 3000 in
private theorem okrr3315_3684 : (List.range' 3315 369).filter (primeBit WheelTableA94.fast) = rr3315_3684 := merge_filter (primeBit WheelTableA94.fast) 3315 184 185 rr3315_3499 rr3499_3684 okrr3315_3499 okrr3499_3684
set_option maxRecDepth 3000 in
private theorem vrr3315_3684 : (rr3315_3684.map term).sum = 35218 := by rw [rr3315_3684,List.map_append,List.sum_append,vrr3315_3499,vrr3499_3684]

private def rr2947_3684 : List ℕ := rr2947_3315 ++ rr3315_3684
set_option maxRecDepth 3000 in
private theorem okrr2947_3684 : (List.range' 2947 737).filter (primeBit WheelTableA94.fast) = rr2947_3684 := merge_filter (primeBit WheelTableA94.fast) 2947 368 369 rr2947_3315 rr3315_3684 okrr2947_3315 okrr3315_3684
set_option maxRecDepth 3000 in
private theorem vrr2947_3684 : (rr2947_3684.map term).sum = 73075 := by rw [rr2947_3684,List.map_append,List.sum_append,vrr2947_3315,vrr3315_3684]

private def rr3684_3868 : List ℕ := [3691,3697,3701,3709,3719,3727,3733,3739,3761,3767,3769,3779,3793,3797,3803,3821,3823,3833,3847,3851,3853,3863]
set_option maxRecDepth 3000 in
private theorem okrr3684_3868 : (List.range' 3684 184).filter (primeBit WheelTableA94.fast) = rr3684_3868 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3684_3868 : (rr3684_3868.map term).sum = 13551 := by decide +kernel

private def rr3868_4052 : List ℕ := [3877,3881,3889,3907,3911,3917,3919,3923,3929,3931,3943,3947,3967,3989,4001,4003,4007,4013,4019,4021,4027,4049,4051]
set_option maxRecDepth 3000 in
private theorem okrr3868_4052 : (List.range' 3868 184).filter (primeBit WheelTableA94.fast) = rr3868_4052 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr3868_4052 : (rr3868_4052.map term).sum = 12542 := by decide +kernel

private def rr3684_4052 : List ℕ := rr3684_3868 ++ rr3868_4052
set_option maxRecDepth 3000 in
private theorem okrr3684_4052 : (List.range' 3684 368).filter (primeBit WheelTableA94.fast) = rr3684_4052 := merge_filter (primeBit WheelTableA94.fast) 3684 184 184 rr3684_3868 rr3868_4052 okrr3684_3868 okrr3868_4052
set_option maxRecDepth 3000 in
private theorem vrr3684_4052 : (rr3684_4052.map term).sum = 26093 := by rw [rr3684_4052,List.map_append,List.sum_append,vrr3684_3868,vrr3868_4052]

private def rr4052_4236 : List ℕ := [4057,4073,4079,4091,4093,4099,4111,4127,4129,4133,4139,4153,4157,4159,4177,4201,4211,4217,4219,4229,4231]
set_option maxRecDepth 3000 in
private theorem okrr4052_4236 : (List.range' 4052 184).filter (primeBit WheelTableA94.fast) = rr4052_4236 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4052_4236 : (rr4052_4236.map term).sum = 10061 := by decide +kernel

private def rr4236_4421 : List ℕ := [4241,4243,4253,4259,4261,4271,4273,4283,4289,4297,4327,4337,4339,4349,4357,4363,4373,4391,4397,4409]
set_option maxRecDepth 3000 in
private theorem okrr4236_4421 : (List.range' 4236 185).filter (primeBit WheelTableA94.fast) = rr4236_4421 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4236_4421 : (rr4236_4421.map term).sum = 8475 := by decide +kernel

private def rr4052_4421 : List ℕ := rr4052_4236 ++ rr4236_4421
set_option maxRecDepth 3000 in
private theorem okrr4052_4421 : (List.range' 4052 369).filter (primeBit WheelTableA94.fast) = rr4052_4421 := merge_filter (primeBit WheelTableA94.fast) 4052 184 185 rr4052_4236 rr4236_4421 okrr4052_4236 okrr4236_4421
set_option maxRecDepth 3000 in
private theorem vrr4052_4421 : (rr4052_4421.map term).sum = 18536 := by rw [rr4052_4421,List.map_append,List.sum_append,vrr4052_4236,vrr4236_4421]

private def rr3684_4421 : List ℕ := rr3684_4052 ++ rr4052_4421
set_option maxRecDepth 3000 in
private theorem okrr3684_4421 : (List.range' 3684 737).filter (primeBit WheelTableA94.fast) = rr3684_4421 := merge_filter (primeBit WheelTableA94.fast) 3684 368 369 rr3684_4052 rr4052_4421 okrr3684_4052 okrr4052_4421
set_option maxRecDepth 3000 in
private theorem vrr3684_4421 : (rr3684_4421.map term).sum = 44629 := by rw [rr3684_4421,List.map_append,List.sum_append,vrr3684_4052,vrr4052_4421]

private def rr2947_4421 : List ℕ := rr2947_3684 ++ rr3684_4421
set_option maxRecDepth 3000 in
private theorem okrr2947_4421 : (List.range' 2947 1474).filter (primeBit WheelTableA94.fast) = rr2947_4421 := merge_filter (primeBit WheelTableA94.fast) 2947 737 737 rr2947_3684 rr3684_4421 okrr2947_3684 okrr3684_4421
set_option maxRecDepth 3000 in
private theorem vrr2947_4421 : (rr2947_4421.map term).sum = 117704 := by rw [rr2947_4421,List.map_append,List.sum_append,vrr2947_3684,vrr3684_4421]

private def rr4421_4605 : List ℕ := [4421,4423,4441,4447,4451,4457,4463,4481,4483,4493,4507,4513,4517,4519,4523,4547,4549,4561,4567,4583,4591,4597,4603]
set_option maxRecDepth 3000 in
private theorem okrr4421_4605 : (List.range' 4421 184).filter (primeBit WheelTableA94.fast) = rr4421_4605 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4421_4605 : (rr4421_4605.map term).sum = 8403 := by decide +kernel

private def rr4605_4789 : List ℕ := [4621,4637,4639,4643,4649,4651,4657,4663,4673,4679,4691,4703,4721,4723,4729,4733,4751,4759,4783,4787]
set_option maxRecDepth 3000 in
private theorem okrr4605_4789 : (List.range' 4605 184).filter (primeBit WheelTableA94.fast) = rr4605_4789 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4605_4789 : (rr4605_4789.map term).sum = 6147 := by decide +kernel

private def rr4421_4789 : List ℕ := rr4421_4605 ++ rr4605_4789
set_option maxRecDepth 3000 in
private theorem okrr4421_4789 : (List.range' 4421 368).filter (primeBit WheelTableA94.fast) = rr4421_4789 := merge_filter (primeBit WheelTableA94.fast) 4421 184 184 rr4421_4605 rr4605_4789 okrr4421_4605 okrr4605_4789
set_option maxRecDepth 3000 in
private theorem vrr4421_4789 : (rr4421_4789.map term).sum = 14550 := by rw [rr4421_4789,List.map_append,List.sum_append,vrr4421_4605,vrr4605_4789]

private def rr4789_4973 : List ℕ := [4789,4793,4799,4801,4813,4817,4831,4861,4871,4877,4889,4903,4909,4919,4931,4933,4937,4943,4951,4957,4967,4969]
set_option maxRecDepth 3000 in
private theorem okrr4789_4973 : (List.range' 4789 184).filter (primeBit WheelTableA94.fast) = rr4789_4973 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4789_4973 : (rr4789_4973.map term).sum = 5688 := by decide +kernel

private def rr4973_5158 : List ℕ := [4973,4987,4993,4999,5003,5009,5011,5021,5023,5039,5051,5059,5077,5081,5087,5099,5101,5107,5113,5119,5147,5153]
set_option maxRecDepth 3000 in
private theorem okrr4973_5158 : (List.range' 4973 185).filter (primeBit WheelTableA94.fast) = rr4973_5158 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr4973_5158 : (rr4973_5158.map term).sum = 4576 := by decide +kernel

private def rr4789_5158 : List ℕ := rr4789_4973 ++ rr4973_5158
set_option maxRecDepth 3000 in
private theorem okrr4789_5158 : (List.range' 4789 369).filter (primeBit WheelTableA94.fast) = rr4789_5158 := merge_filter (primeBit WheelTableA94.fast) 4789 184 185 rr4789_4973 rr4973_5158 okrr4789_4973 okrr4973_5158
set_option maxRecDepth 3000 in
private theorem vrr4789_5158 : (rr4789_5158.map term).sum = 10264 := by rw [rr4789_5158,List.map_append,List.sum_append,vrr4789_4973,vrr4973_5158]

private def rr4421_5158 : List ℕ := rr4421_4789 ++ rr4789_5158
set_option maxRecDepth 3000 in
private theorem okrr4421_5158 : (List.range' 4421 737).filter (primeBit WheelTableA94.fast) = rr4421_5158 := merge_filter (primeBit WheelTableA94.fast) 4421 368 369 rr4421_4789 rr4789_5158 okrr4421_4789 okrr4789_5158
set_option maxRecDepth 3000 in
private theorem vrr4421_5158 : (rr4421_5158.map term).sum = 24814 := by rw [rr4421_5158,List.map_append,List.sum_append,vrr4421_4789,vrr4789_5158]

private def rr5158_5342 : List ℕ := [5167,5171,5179,5189,5197,5209,5227,5231,5233,5237,5261,5273,5279,5281,5297,5303,5309,5323,5333]
set_option maxRecDepth 3000 in
private theorem okrr5158_5342 : (List.range' 5158 184).filter (primeBit WheelTableA94.fast) = rr5158_5342 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr5158_5342 : (rr5158_5342.map term).sum = 3013 := by decide +kernel

private def rr5342_5526 : List ℕ := [5347,5351,5381,5387,5393,5399,5407,5413,5417,5419,5431,5437,5441,5443,5449,5471,5477,5479,5483,5501,5503,5507,5519,5521]
set_option maxRecDepth 3000 in
private theorem okrr5342_5526 : (List.range' 5342 184).filter (primeBit WheelTableA94.fast) = rr5342_5526 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr5342_5526 : (rr5342_5526.map term).sum = 2712 := by decide +kernel

private def rr5158_5526 : List ℕ := rr5158_5342 ++ rr5342_5526
set_option maxRecDepth 3000 in
private theorem okrr5158_5526 : (List.range' 5158 368).filter (primeBit WheelTableA94.fast) = rr5158_5526 := merge_filter (primeBit WheelTableA94.fast) 5158 184 184 rr5158_5342 rr5342_5526 okrr5158_5342 okrr5342_5526
set_option maxRecDepth 3000 in
private theorem vrr5158_5526 : (rr5158_5526.map term).sum = 5725 := by rw [rr5158_5526,List.map_append,List.sum_append,vrr5158_5342,vrr5342_5526]

private def rr5526_5710 : List ℕ := [5527,5531,5557,5563,5569,5573,5581,5591,5623,5639,5641,5647,5651,5653,5657,5659,5669,5683,5689,5693,5701]
set_option maxRecDepth 3000 in
private theorem okrr5526_5710 : (List.range' 5526 184).filter (primeBit WheelTableA94.fast) = rr5526_5710 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr5526_5710 : (rr5526_5710.map term).sum = 1353 := by decide +kernel

private def rr5710_5895 : List ℕ := [5711,5717,5737,5741,5743,5749,5779,5783,5791,5801,5807,5813,5821,5827,5839,5843,5849,5851,5857,5861,5867,5869,5879,5881]
set_option maxRecDepth 3000 in
private theorem okrr5710_5895 : (List.range' 5710 185).filter (primeBit WheelTableA94.fast) = rr5710_5895 := by decide +kernel
set_option maxRecDepth 3000 in
private theorem vrr5710_5895 : (rr5710_5895.map term).sum = 489 := by decide +kernel

private def rr5526_5895 : List ℕ := rr5526_5710 ++ rr5710_5895
set_option maxRecDepth 3000 in
private theorem okrr5526_5895 : (List.range' 5526 369).filter (primeBit WheelTableA94.fast) = rr5526_5895 := merge_filter (primeBit WheelTableA94.fast) 5526 184 185 rr5526_5710 rr5710_5895 okrr5526_5710 okrr5710_5895
set_option maxRecDepth 3000 in
private theorem vrr5526_5895 : (rr5526_5895.map term).sum = 1842 := by rw [rr5526_5895,List.map_append,List.sum_append,vrr5526_5710,vrr5710_5895]

private def rr5158_5895 : List ℕ := rr5158_5526 ++ rr5526_5895
set_option maxRecDepth 3000 in
private theorem okrr5158_5895 : (List.range' 5158 737).filter (primeBit WheelTableA94.fast) = rr5158_5895 := merge_filter (primeBit WheelTableA94.fast) 5158 368 369 rr5158_5526 rr5526_5895 okrr5158_5526 okrr5526_5895
set_option maxRecDepth 3000 in
private theorem vrr5158_5895 : (rr5158_5895.map term).sum = 7567 := by rw [rr5158_5895,List.map_append,List.sum_append,vrr5158_5526,vrr5526_5895]

private def rr4421_5895 : List ℕ := rr4421_5158 ++ rr5158_5895
set_option maxRecDepth 3000 in
private theorem okrr4421_5895 : (List.range' 4421 1474).filter (primeBit WheelTableA94.fast) = rr4421_5895 := merge_filter (primeBit WheelTableA94.fast) 4421 737 737 rr4421_5158 rr5158_5895 okrr4421_5158 okrr5158_5895
set_option maxRecDepth 3000 in
private theorem vrr4421_5895 : (rr4421_5895.map term).sum = 32381 := by rw [rr4421_5895,List.map_append,List.sum_append,vrr4421_5158,vrr5158_5895]

private def rr2947_5895 : List ℕ := rr2947_4421 ++ rr4421_5895
set_option maxRecDepth 3000 in
private theorem okrr2947_5895 : (List.range' 2947 2948).filter (primeBit WheelTableA94.fast) = rr2947_5895 := merge_filter (primeBit WheelTableA94.fast) 2947 1474 1474 rr2947_4421 rr4421_5895 okrr2947_4421 okrr4421_5895
set_option maxRecDepth 3000 in
private theorem vrr2947_5895 : (rr2947_5895.map term).sum = 150085 := by rw [rr2947_5895,List.map_append,List.sum_append,vrr2947_4421,vrr4421_5895]

private def rr0_5895 : List ℕ := rr0_2947 ++ rr2947_5895
set_option maxRecDepth 3000 in
private theorem okrr0_5895 : (List.range' 0 5895).filter (primeBit WheelTableA94.fast) = rr0_5895 := merge_filter (primeBit WheelTableA94.fast) 0 2947 2948 rr0_2947 rr2947_5895 okrr0_2947 okrr2947_5895
set_option maxRecDepth 3000 in
private theorem vrr0_5895 : (rr0_5895.map term).sum = 1230644 := by rw [rr0_5895,List.map_append,List.sum_append,vrr0_2947,vrr2947_5895]

private theorem right_part :
    (∑ p ∈ (Nat.primesLE 5894).filter (326 < ·), (Nat.primeCounting (34751024/p) - Nat.primeCounting (p-1))) = 1230644 := by
  have rows : (List.range (5894+1)).filter (fun p => decide p.Prime) = rr0_5895 := by
    rw [filter_bits WheelTableA94.fast WheelTableA94.fast_correct _ (by decide),List.range_eq_range']
    exact okrr0_5895
  have nd : rr0_5895.Nodup := by rw [←rows]; exact List.nodup_range.filter _
  have same : Nat.primesLE 5894 = rr0_5895.toFinset := by
    rw [←rows]
    ext n
    simp [Nat.mem_primesLE]
    omega
  calc
    _ = ∑ p ∈ (Nat.primesLE 5894).filter (326<·), (WheelTableA94.fast (34751024/p)-WheelTableA94.fast (p-1)) := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨mem,above⟩ := Finset.mem_filter.mp hp
      have ub := Nat.le_of_mem_primesLE mem
      have lim : 34751024/p ≤ 106272 :=
        Nat.div_le_div_left (show 327 ≤ p by omega) (by decide)
      rw [WheelTableA94.fast_correct _ (by omega),WheelTableA94.fast_correct _ (by omega)]
    _ = (rr0_5895.map term).sum := by
      rw [same,Finset.sum_filter]
      exact List.sum_toFinset term nd
    _ = _ := vrr0_5895

set_option maxRecDepth 12000 in
theorem first_anchor : Nat.primeCounting 34751024 = 2132375 :=
  assemble (x:=34751024) (y:=326) (z:=5894) (a:=3363020) (b:=1230644) (r:=2132375)
    (by decide) (by decide) (by decide) (by decide) (by decide) left_part right_part (by decide)
end RankWheel34751


/- Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace FastDenseControl

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


private def packet (i : ℕ) : ℕ := (if i < 2 then (if i < 1 then 0x3ab60e119d9b6d2b63403944308218d32405aae037a522434c0a262c7570360b01689d1784d8c180345ada9c22287ce24050328618302abcad593d2030c2770494d45aa5a8602f214089851b7e3556002d62e1568bf88056a0702b99c742f3ad40648d102a0c41e22a6502b962402838dea735ca89501190266f8246c44cbf10b43024b307a4c570c944ab2022f02cdcdb50238f12c0211c383dc8219f6264e01f44c58b42aa71c8b5a01d64d33f3243e88518d01b999eb813c26c73811019ea0e3266581d892d2017b87588f9265aefb720162468c83e5081a96540142ef17c19b7171582101224f8cbcc8b37ac18c010454bf11453a2b4cb800e13a13f666e944fd2e00c1f8a154039ff0a3d9009f554c2ade2dade356007d56a61e78bd92676a0059a559dd3bd3d30ce600319eeda6eaf31e4fd50000f93ddbb67eefdffe else 0x6e2a1aab3e1522a44b506cc155941180896a81606b0b1474266d75888980693f40c0fd888a13367068030831c4901c11218066ae8021d1461b0180d064c5c788582a4742d9f0635a08ac312424892d5061f073110366302a4b006041b6614e808d83c6a05ebc476e0092ca50a6105ce4a84d62d2a8b935605b3c319653818c126cd059b91500ec0f60c2e06057e15a9d8d2182f54f0056a0931a610461a818205518bc61a44c88c27220536c760421da13859b20520104ac2b029c3d3000506a508e9861b26568204ee818992787024225d04d24c8ed84446e5c16c04bbb430300a25c31934049de34730e982b129e904831006c514dc3dcb1404672e644e1194e3471a044f2902ac8f81c5680a04301cb59861572ae6c3041838b14873440319e003fc32c8231e685da12703e5105574a88388099a03ca947a44d060391a67) else (if i < 3 then 0x9f0b7484c511415c01609d61a8596b4a171c00e09c12d050c8b409530c009a8197c9080613a698c098ed9364b110a8445650976866253324449301d095ab2f02e6f10089770094214780a82150eaae109291483817d0c62a4720913c280308cf932444108fe912809c930700d0608e5e0bb5812248c845908c938db21462d1ccc9208afc1834c29426c92b3089804002a54cd032bd3087d7e47c008a48aa32e08690c518403e11464280856903c80a0805a42c40841c525021058098e490827076a4626448f309c080d6b2520cf8291bc0807f33730adc5093211c107dd328a0cb018b1e12007bfa3d629317a25562c07aa022439c28252c20b0790750b88570ce409c407791063206c478c980b076250a0560e57012ca8074c840a61d07801915607347e08150c826b362007170ad654be00673ca306ff0ca5111855624559 else 0xac200ca1712421c40b60aad4872222704a918880a9923548144410652a10a866061d12c829004060a69a851a1197b5528e30a4f471023aae20ec48b0a335c2033c078e91eb40a20220891108190d51c0a08a1022e8a89109579))


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


private def radical : ℕ := 35375166993717494840635767087951744212057570647889977422429870

private def light (n : ℕ) : Bool :=
  if n≤12 then decide n.Prime else n.gcd 479001600 == 1

private theorem light_ok {n : ℕ} (hn : n≤158) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 12 = 479001600 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 12 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤158 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 39 := by unfold smallValid; decide +kernel

private theorem sp39 : smallValid 39 40 := by unfold smallValid; decide +kernel

private theorem sp79 : smallValid 79 40 := by unfold smallValid; decide +kernel

private theorem sp119 : smallValid 119 40 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤158) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 159 := (joinSmall (lo:=0) (a:=79) (b:=80) (joinSmall (lo:=0) (a:=39) (b:=40) sp0 sp39) (joinSmall (lo:=79) (a:=40) (b:=40) sp79 sp119))
  have good : (List.range 159).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 25123) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 158 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 158 := by
        by_contra! hi
        have hb := Nat.mul_le_mul hi hi
        rw [pow_two] at hsq
        omega
      have hd := Nat.dvd_gcd (Nat.minFac_dvd n) (smallPrimeDvd n.minFac hfac hpr)
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



private theorem d0 : covered 0 839 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d839 : covered 839 1678 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d1678 : covered 1678 2517 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d2517 : covered 2517 3356 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d3356 : covered 3356 4195 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d4195 : covered 4195 5034 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d5034 : covered 5034 5873 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d5873 : covered 5873 6712 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 0 6712 := (joinCoverage (joinCoverage (joinCoverage d0 d839) (joinCoverage d1678 d2517)) (joinCoverage (joinCoverage d3356 d4195) (joinCoverage d5034 d5873)))

theorem fast_correct (n : ℕ) (bound : n ≤ 25123) : fast n = Nat.primeCounting n := by
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
      · have ix := index_bound (show n≤25123 by omega)
        have h := beq_iff_eq.mp (allrows (index n) (Nat.zero_le _) ix)
        change raw (index n+1) = raw (index n) + (if quick (number (index n)) then 1 else 0) at h
        rw [whose] at h
        simp only [fast,e,h,unchanged]
        by_cases hp : (n+1).Prime
        · simp [hp,(quick_ok bound).mpr hp,Nat.add_right_comm]
        · simp [hp,mt (quick_ok bound).mp hp]
def prime (n : ℕ) : Bool := quick n
theorem prime_ok (n : ℕ) (hn : n≤25123) : prime n=true ↔ n.Prime := quick_ok hn
end FastDenseControl


/- Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace RangePrimeA26

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




private def radical : ℕ := 133438758377827279449163953778114585212136061343584163723230013362887979787651669016112679250309162896407493408926967418946550243176078181301045260088965295509156510786071918404851953512934606156281659971269428429158711244538069182469304953191664134397735271931136516324465528908419069339805902464946959936083473325604310329755229913535044488910904961441454959671114434266923553167505316015743899509307798101316855255578696315758306460003423820665325180360000953550756365762551481761263582099929255184371915180823683958721296171095904817610894264058639199781265949656194813838755800318008893565294543235189610851241581562782070921349299208430247571726692374226828337218439002177074512338194981274411006927232308899852791334404924807246821033288295611902356993668855423423361972881682326117574913400869321037431225461996971147572148791387833434296766700090415982598632585580671504534787271309590848020739727579364347876642823328614991730037415329149368792452597777164785232007343879046469512194634856893996550241772033507799409324250726388741048935855446371679016883908882849911290099891209394809573638134523413120690887544274687136560788467861471640070792983644138219159915930871625752112709968448022583767935643802994149068873450229008058063695776431197601761898492049741829636588662632627463934455517241295303091462443854851332988311905638622810743349167988723572492898579978081098983094383717681756007939623845354252280662613955583573824028815501305416556840751743728737003439342317331441953964885873776583228475167255415438257466859935836453488773628875888033482263154164669364705000404968642572412917772637939530090880017423821300732930802624217873941966695281735434158684690752475755860242689341528961043156063338337221439464465333600249151339862545293307150613348129222645976323819285544136918769788699060843637101150803117280522656634499252725778863425494340800593758588951596215626928319474662625002063286547472318868371136570710731037831402523750468835699569997336810577094372529754595169236379347314444841240398618319015358159670464164992452048583767424788767254847283925904220693793757479991362264446743655705329487959608347044300326531466169892439829713975686994165217448369867451446613460703903805499485425751383409323823717231787163710297503175843574303640703315368944821625205676225768216325692951154681092280858037479229665081078294536311954479893961972686510287210258074816525820723575297110273757548921532944414209817093820330139576051573113186273560608330173396704987171244478273462285529949162869958055202956179652310990952406189955582903450378017992865811177908185029530903492543205965806455917350739252664759518014115885360006583058157895530616035741063927940540531315417865845251739917297236693846992674801759461776661361818407747050695408127552661850776429229264425431294797061900320577646956099427736620439445109434389082966170975705927125515261921075939384181254598792722085374582127860868210626997465537246584253297513212439166012854136435131803547507582039546626943731185186147890167966781213944704008272716553311087929000739968523577028631205193918665000258553460722880702980699220318399219913291832993163274876441109684174062954854098101147342545789744246691635082588863589840493533840832429921306863936872459556256185873052555506998427572965773435535569452063405837537540311287641191136356091596796522670214586433679590033177553979929610543830837413715554000856574859650140441330378415107205171363657700484171927839800509482433396352493531938101310183946329243515387736461890

private def light (n : ℕ) : Bool :=
  if n≤90 then decide n.Prime else n.gcd 1485715964481761497309522733620825737885569961284688766942216863704985393094065876545992131370884059645617234469978112000000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤8218) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 90 = 1485715964481761497309522733620825737885569961284688766942216863704985393094065876545992131370884059645617234469978112000000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 90 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤8218 then light n else n.gcd radical == 1

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

private theorem sp3273 : smallValid 3273 32 := by unfold smallValid; decide +kernel

private theorem sp3305 : smallValid 3305 33 := by unfold smallValid; decide +kernel

private theorem sp3338 : smallValid 3338 64 := by unfold smallValid; decide +kernel

private theorem sp3402 : smallValid 3402 64 := by unfold smallValid; decide +kernel

private theorem sp3466 : smallValid 3466 64 := by unfold smallValid; decide +kernel

private theorem sp3530 : smallValid 3530 32 := by unfold smallValid; decide +kernel

private theorem sp3562 : smallValid 3562 33 := by unfold smallValid; decide +kernel

private theorem sp3595 : smallValid 3595 64 := by unfold smallValid; decide +kernel

private theorem sp3659 : smallValid 3659 64 := by unfold smallValid; decide +kernel

private theorem sp3723 : smallValid 3723 64 := by unfold smallValid; decide +kernel

private theorem sp3787 : smallValid 3787 32 := by unfold smallValid; decide +kernel

private theorem sp3819 : smallValid 3819 33 := by unfold smallValid; decide +kernel

private theorem sp3852 : smallValid 3852 64 := by unfold smallValid; decide +kernel

private theorem sp3916 : smallValid 3916 64 := by unfold smallValid; decide +kernel

private theorem sp3980 : smallValid 3980 64 := by unfold smallValid; decide +kernel

private theorem sp4044 : smallValid 4044 32 := by unfold smallValid; decide +kernel

private theorem sp4076 : smallValid 4076 33 := by unfold smallValid; decide +kernel

private theorem sp4109 : smallValid 4109 64 := by unfold smallValid; decide +kernel

private theorem sp4173 : smallValid 4173 64 := by unfold smallValid; decide +kernel

private theorem sp4237 : smallValid 4237 64 := by unfold smallValid; decide +kernel

private theorem sp4301 : smallValid 4301 64 := by unfold smallValid; decide +kernel

private theorem sp4365 : smallValid 4365 64 := by unfold smallValid; decide +kernel

private theorem sp4429 : smallValid 4429 64 := by unfold smallValid; decide +kernel

private theorem sp4493 : smallValid 4493 64 := by unfold smallValid; decide +kernel

private theorem sp4557 : smallValid 4557 32 := by unfold smallValid; decide +kernel

private theorem sp4589 : smallValid 4589 33 := by unfold smallValid; decide +kernel

private theorem sp4622 : smallValid 4622 64 := by unfold smallValid; decide +kernel

private theorem sp4686 : smallValid 4686 64 := by unfold smallValid; decide +kernel

private theorem sp4750 : smallValid 4750 64 := by unfold smallValid; decide +kernel

private theorem sp4814 : smallValid 4814 32 := by unfold smallValid; decide +kernel

private theorem sp4846 : smallValid 4846 33 := by unfold smallValid; decide +kernel

private theorem sp4879 : smallValid 4879 64 := by unfold smallValid; decide +kernel

private theorem sp4943 : smallValid 4943 64 := by unfold smallValid; decide +kernel

private theorem sp5007 : smallValid 5007 64 := by unfold smallValid; decide +kernel

private theorem sp5071 : smallValid 5071 32 := by unfold smallValid; decide +kernel

private theorem sp5103 : smallValid 5103 33 := by unfold smallValid; decide +kernel

private theorem sp5136 : smallValid 5136 64 := by unfold smallValid; decide +kernel

private theorem sp5200 : smallValid 5200 64 := by unfold smallValid; decide +kernel

private theorem sp5264 : smallValid 5264 64 := by unfold smallValid; decide +kernel

private theorem sp5328 : smallValid 5328 32 := by unfold smallValid; decide +kernel

private theorem sp5360 : smallValid 5360 33 := by unfold smallValid; decide +kernel

private theorem sp5393 : smallValid 5393 64 := by unfold smallValid; decide +kernel

private theorem sp5457 : smallValid 5457 64 := by unfold smallValid; decide +kernel

private theorem sp5521 : smallValid 5521 64 := by unfold smallValid; decide +kernel

private theorem sp5585 : smallValid 5585 32 := by unfold smallValid; decide +kernel

private theorem sp5617 : smallValid 5617 33 := by unfold smallValid; decide +kernel

private theorem sp5650 : smallValid 5650 64 := by unfold smallValid; decide +kernel

private theorem sp5714 : smallValid 5714 64 := by unfold smallValid; decide +kernel

private theorem sp5778 : smallValid 5778 64 := by unfold smallValid; decide +kernel

private theorem sp5842 : smallValid 5842 32 := by unfold smallValid; decide +kernel

private theorem sp5874 : smallValid 5874 33 := by unfold smallValid; decide +kernel

private theorem sp5907 : smallValid 5907 64 := by unfold smallValid; decide +kernel

private theorem sp5971 : smallValid 5971 64 := by unfold smallValid; decide +kernel

private theorem sp6035 : smallValid 6035 64 := by unfold smallValid; decide +kernel

private theorem sp6099 : smallValid 6099 32 := by unfold smallValid; decide +kernel

private theorem sp6131 : smallValid 6131 33 := by unfold smallValid; decide +kernel

private theorem sp6164 : smallValid 6164 64 := by unfold smallValid; decide +kernel

private theorem sp6228 : smallValid 6228 64 := by unfold smallValid; decide +kernel

private theorem sp6292 : smallValid 6292 64 := by unfold smallValid; decide +kernel

private theorem sp6356 : smallValid 6356 64 := by unfold smallValid; decide +kernel

private theorem sp6420 : smallValid 6420 64 := by unfold smallValid; decide +kernel

private theorem sp6484 : smallValid 6484 64 := by unfold smallValid; decide +kernel

private theorem sp6548 : smallValid 6548 64 := by unfold smallValid; decide +kernel

private theorem sp6612 : smallValid 6612 32 := by unfold smallValid; decide +kernel

private theorem sp6644 : smallValid 6644 33 := by unfold smallValid; decide +kernel

private theorem sp6677 : smallValid 6677 64 := by unfold smallValid; decide +kernel

private theorem sp6741 : smallValid 6741 64 := by unfold smallValid; decide +kernel

private theorem sp6805 : smallValid 6805 64 := by unfold smallValid; decide +kernel

private theorem sp6869 : smallValid 6869 32 := by unfold smallValid; decide +kernel

private theorem sp6901 : smallValid 6901 33 := by unfold smallValid; decide +kernel

private theorem sp6934 : smallValid 6934 64 := by unfold smallValid; decide +kernel

private theorem sp6998 : smallValid 6998 64 := by unfold smallValid; decide +kernel

private theorem sp7062 : smallValid 7062 64 := by unfold smallValid; decide +kernel

private theorem sp7126 : smallValid 7126 32 := by unfold smallValid; decide +kernel

private theorem sp7158 : smallValid 7158 33 := by unfold smallValid; decide +kernel

private theorem sp7191 : smallValid 7191 64 := by unfold smallValid; decide +kernel

private theorem sp7255 : smallValid 7255 64 := by unfold smallValid; decide +kernel

private theorem sp7319 : smallValid 7319 64 := by unfold smallValid; decide +kernel

private theorem sp7383 : smallValid 7383 32 := by unfold smallValid; decide +kernel

private theorem sp7415 : smallValid 7415 33 := by unfold smallValid; decide +kernel

private theorem sp7448 : smallValid 7448 64 := by unfold smallValid; decide +kernel

private theorem sp7512 : smallValid 7512 64 := by unfold smallValid; decide +kernel

private theorem sp7576 : smallValid 7576 64 := by unfold smallValid; decide +kernel

private theorem sp7640 : smallValid 7640 32 := by unfold smallValid; decide +kernel

private theorem sp7672 : smallValid 7672 33 := by unfold smallValid; decide +kernel

private theorem sp7705 : smallValid 7705 64 := by unfold smallValid; decide +kernel

private theorem sp7769 : smallValid 7769 64 := by unfold smallValid; decide +kernel

private theorem sp7833 : smallValid 7833 64 := by unfold smallValid; decide +kernel

private theorem sp7897 : smallValid 7897 32 := by unfold smallValid; decide +kernel

private theorem sp7929 : smallValid 7929 33 := by unfold smallValid; decide +kernel

private theorem sp7962 : smallValid 7962 64 := by unfold smallValid; decide +kernel

private theorem sp8026 : smallValid 8026 64 := by unfold smallValid; decide +kernel

private theorem sp8090 : smallValid 8090 64 := by unfold smallValid; decide +kernel

private theorem sp8154 : smallValid 8154 32 := by unfold smallValid; decide +kernel

private theorem sp8186 : smallValid 8186 33 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤8218) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 8219 := (joinSmall (lo:=0) (a:=4109) (b:=4110) (joinSmall (lo:=0) (a:=2054) (b:=2055) (joinSmall (lo:=0) (a:=1027) (b:=1027) (joinSmall (lo:=0) (a:=513) (b:=514) (joinSmall (lo:=0) (a:=256) (b:=257) (joinSmall (lo:=0) (a:=128) (b:=128) (joinSmall (lo:=0) (a:=64) (b:=64) sp0 sp64) (joinSmall (lo:=128) (a:=64) (b:=64) sp128 sp192)) (joinSmall (lo:=256) (a:=128) (b:=129) (joinSmall (lo:=256) (a:=64) (b:=64) sp256 sp320) (joinSmall (lo:=384) (a:=64) (b:=65) sp384 (joinSmall (lo:=448) (a:=32) (b:=33) sp448 sp480)))) (joinSmall (lo:=513) (a:=257) (b:=257) (joinSmall (lo:=513) (a:=128) (b:=129) (joinSmall (lo:=513) (a:=64) (b:=64) sp513 sp577) (joinSmall (lo:=641) (a:=64) (b:=65) sp641 (joinSmall (lo:=705) (a:=32) (b:=33) sp705 sp737))) (joinSmall (lo:=770) (a:=128) (b:=129) (joinSmall (lo:=770) (a:=64) (b:=64) sp770 sp834) (joinSmall (lo:=898) (a:=64) (b:=65) sp898 (joinSmall (lo:=962) (a:=32) (b:=33) sp962 sp994))))) (joinSmall (lo:=1027) (a:=513) (b:=514) (joinSmall (lo:=1027) (a:=256) (b:=257) (joinSmall (lo:=1027) (a:=128) (b:=128) (joinSmall (lo:=1027) (a:=64) (b:=64) sp1027 sp1091) (joinSmall (lo:=1155) (a:=64) (b:=64) sp1155 sp1219)) (joinSmall (lo:=1283) (a:=128) (b:=129) (joinSmall (lo:=1283) (a:=64) (b:=64) sp1283 sp1347) (joinSmall (lo:=1411) (a:=64) (b:=65) sp1411 (joinSmall (lo:=1475) (a:=32) (b:=33) sp1475 sp1507)))) (joinSmall (lo:=1540) (a:=257) (b:=257) (joinSmall (lo:=1540) (a:=128) (b:=129) (joinSmall (lo:=1540) (a:=64) (b:=64) sp1540 sp1604) (joinSmall (lo:=1668) (a:=64) (b:=65) sp1668 (joinSmall (lo:=1732) (a:=32) (b:=33) sp1732 sp1764))) (joinSmall (lo:=1797) (a:=128) (b:=129) (joinSmall (lo:=1797) (a:=64) (b:=64) sp1797 sp1861) (joinSmall (lo:=1925) (a:=64) (b:=65) sp1925 (joinSmall (lo:=1989) (a:=32) (b:=33) sp1989 sp2021)))))) (joinSmall (lo:=2054) (a:=1027) (b:=1028) (joinSmall (lo:=2054) (a:=513) (b:=514) (joinSmall (lo:=2054) (a:=256) (b:=257) (joinSmall (lo:=2054) (a:=128) (b:=128) (joinSmall (lo:=2054) (a:=64) (b:=64) sp2054 sp2118) (joinSmall (lo:=2182) (a:=64) (b:=64) sp2182 sp2246)) (joinSmall (lo:=2310) (a:=128) (b:=129) (joinSmall (lo:=2310) (a:=64) (b:=64) sp2310 sp2374) (joinSmall (lo:=2438) (a:=64) (b:=65) sp2438 (joinSmall (lo:=2502) (a:=32) (b:=33) sp2502 sp2534)))) (joinSmall (lo:=2567) (a:=257) (b:=257) (joinSmall (lo:=2567) (a:=128) (b:=129) (joinSmall (lo:=2567) (a:=64) (b:=64) sp2567 sp2631) (joinSmall (lo:=2695) (a:=64) (b:=65) sp2695 (joinSmall (lo:=2759) (a:=32) (b:=33) sp2759 sp2791))) (joinSmall (lo:=2824) (a:=128) (b:=129) (joinSmall (lo:=2824) (a:=64) (b:=64) sp2824 sp2888) (joinSmall (lo:=2952) (a:=64) (b:=65) sp2952 (joinSmall (lo:=3016) (a:=32) (b:=33) sp3016 sp3048))))) (joinSmall (lo:=3081) (a:=514) (b:=514) (joinSmall (lo:=3081) (a:=257) (b:=257) (joinSmall (lo:=3081) (a:=128) (b:=129) (joinSmall (lo:=3081) (a:=64) (b:=64) sp3081 sp3145) (joinSmall (lo:=3209) (a:=64) (b:=65) sp3209 (joinSmall (lo:=3273) (a:=32) (b:=33) sp3273 sp3305))) (joinSmall (lo:=3338) (a:=128) (b:=129) (joinSmall (lo:=3338) (a:=64) (b:=64) sp3338 sp3402) (joinSmall (lo:=3466) (a:=64) (b:=65) sp3466 (joinSmall (lo:=3530) (a:=32) (b:=33) sp3530 sp3562)))) (joinSmall (lo:=3595) (a:=257) (b:=257) (joinSmall (lo:=3595) (a:=128) (b:=129) (joinSmall (lo:=3595) (a:=64) (b:=64) sp3595 sp3659) (joinSmall (lo:=3723) (a:=64) (b:=65) sp3723 (joinSmall (lo:=3787) (a:=32) (b:=33) sp3787 sp3819))) (joinSmall (lo:=3852) (a:=128) (b:=129) (joinSmall (lo:=3852) (a:=64) (b:=64) sp3852 sp3916) (joinSmall (lo:=3980) (a:=64) (b:=65) sp3980 (joinSmall (lo:=4044) (a:=32) (b:=33) sp4044 sp4076))))))) (joinSmall (lo:=4109) (a:=2055) (b:=2055) (joinSmall (lo:=4109) (a:=1027) (b:=1028) (joinSmall (lo:=4109) (a:=513) (b:=514) (joinSmall (lo:=4109) (a:=256) (b:=257) (joinSmall (lo:=4109) (a:=128) (b:=128) (joinSmall (lo:=4109) (a:=64) (b:=64) sp4109 sp4173) (joinSmall (lo:=4237) (a:=64) (b:=64) sp4237 sp4301)) (joinSmall (lo:=4365) (a:=128) (b:=129) (joinSmall (lo:=4365) (a:=64) (b:=64) sp4365 sp4429) (joinSmall (lo:=4493) (a:=64) (b:=65) sp4493 (joinSmall (lo:=4557) (a:=32) (b:=33) sp4557 sp4589)))) (joinSmall (lo:=4622) (a:=257) (b:=257) (joinSmall (lo:=4622) (a:=128) (b:=129) (joinSmall (lo:=4622) (a:=64) (b:=64) sp4622 sp4686) (joinSmall (lo:=4750) (a:=64) (b:=65) sp4750 (joinSmall (lo:=4814) (a:=32) (b:=33) sp4814 sp4846))) (joinSmall (lo:=4879) (a:=128) (b:=129) (joinSmall (lo:=4879) (a:=64) (b:=64) sp4879 sp4943) (joinSmall (lo:=5007) (a:=64) (b:=65) sp5007 (joinSmall (lo:=5071) (a:=32) (b:=33) sp5071 sp5103))))) (joinSmall (lo:=5136) (a:=514) (b:=514) (joinSmall (lo:=5136) (a:=257) (b:=257) (joinSmall (lo:=5136) (a:=128) (b:=129) (joinSmall (lo:=5136) (a:=64) (b:=64) sp5136 sp5200) (joinSmall (lo:=5264) (a:=64) (b:=65) sp5264 (joinSmall (lo:=5328) (a:=32) (b:=33) sp5328 sp5360))) (joinSmall (lo:=5393) (a:=128) (b:=129) (joinSmall (lo:=5393) (a:=64) (b:=64) sp5393 sp5457) (joinSmall (lo:=5521) (a:=64) (b:=65) sp5521 (joinSmall (lo:=5585) (a:=32) (b:=33) sp5585 sp5617)))) (joinSmall (lo:=5650) (a:=257) (b:=257) (joinSmall (lo:=5650) (a:=128) (b:=129) (joinSmall (lo:=5650) (a:=64) (b:=64) sp5650 sp5714) (joinSmall (lo:=5778) (a:=64) (b:=65) sp5778 (joinSmall (lo:=5842) (a:=32) (b:=33) sp5842 sp5874))) (joinSmall (lo:=5907) (a:=128) (b:=129) (joinSmall (lo:=5907) (a:=64) (b:=64) sp5907 sp5971) (joinSmall (lo:=6035) (a:=64) (b:=65) sp6035 (joinSmall (lo:=6099) (a:=32) (b:=33) sp6099 sp6131)))))) (joinSmall (lo:=6164) (a:=1027) (b:=1028) (joinSmall (lo:=6164) (a:=513) (b:=514) (joinSmall (lo:=6164) (a:=256) (b:=257) (joinSmall (lo:=6164) (a:=128) (b:=128) (joinSmall (lo:=6164) (a:=64) (b:=64) sp6164 sp6228) (joinSmall (lo:=6292) (a:=64) (b:=64) sp6292 sp6356)) (joinSmall (lo:=6420) (a:=128) (b:=129) (joinSmall (lo:=6420) (a:=64) (b:=64) sp6420 sp6484) (joinSmall (lo:=6548) (a:=64) (b:=65) sp6548 (joinSmall (lo:=6612) (a:=32) (b:=33) sp6612 sp6644)))) (joinSmall (lo:=6677) (a:=257) (b:=257) (joinSmall (lo:=6677) (a:=128) (b:=129) (joinSmall (lo:=6677) (a:=64) (b:=64) sp6677 sp6741) (joinSmall (lo:=6805) (a:=64) (b:=65) sp6805 (joinSmall (lo:=6869) (a:=32) (b:=33) sp6869 sp6901))) (joinSmall (lo:=6934) (a:=128) (b:=129) (joinSmall (lo:=6934) (a:=64) (b:=64) sp6934 sp6998) (joinSmall (lo:=7062) (a:=64) (b:=65) sp7062 (joinSmall (lo:=7126) (a:=32) (b:=33) sp7126 sp7158))))) (joinSmall (lo:=7191) (a:=514) (b:=514) (joinSmall (lo:=7191) (a:=257) (b:=257) (joinSmall (lo:=7191) (a:=128) (b:=129) (joinSmall (lo:=7191) (a:=64) (b:=64) sp7191 sp7255) (joinSmall (lo:=7319) (a:=64) (b:=65) sp7319 (joinSmall (lo:=7383) (a:=32) (b:=33) sp7383 sp7415))) (joinSmall (lo:=7448) (a:=128) (b:=129) (joinSmall (lo:=7448) (a:=64) (b:=64) sp7448 sp7512) (joinSmall (lo:=7576) (a:=64) (b:=65) sp7576 (joinSmall (lo:=7640) (a:=32) (b:=33) sp7640 sp7672)))) (joinSmall (lo:=7705) (a:=257) (b:=257) (joinSmall (lo:=7705) (a:=128) (b:=129) (joinSmall (lo:=7705) (a:=64) (b:=64) sp7705 sp7769) (joinSmall (lo:=7833) (a:=64) (b:=65) sp7833 (joinSmall (lo:=7897) (a:=32) (b:=33) sp7897 sp7929))) (joinSmall (lo:=7962) (a:=128) (b:=129) (joinSmall (lo:=7962) (a:=64) (b:=64) sp7962 sp8026) (joinSmall (lo:=8090) (a:=64) (b:=65) sp8090 (joinSmall (lo:=8154) (a:=32) (b:=33) sp8154 sp8186))))))))
  have good : (List.range 8219).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 67545646) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 8218 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 8218 := by
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


private def packet (i : ℕ) : ℕ := (if i < 17 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0 else 0) else (if i < 3 then 0 else 0)) else (if i < 6 then (if i < 5 then 0 else 0) else (if i < 7 then 0 else 0))) else (if i < 12 then (if i < 10 then (if i < 9 then 0 else 0) else (if i < 11 then 0 else 0)) else (if i < 14 then (if i < 13 then 0 else 0) else (if i < 15 then 0 else (if i < 16 then 0 else 0))))) else (if i < 26 then (if i < 21 then (if i < 19 then (if i < 18 then 0x21124d345185cb4e53226191347b83751808a584421c30ab83640d6000210b7d3349804b3652f26511487d03791848a6c4681bc0ab83840da000210482344988cb68548265118c7f03811888a784461b80a4834c0d000020fdb832797a0b0851b25610c079635316f09e441c1a70a003640cc00020f6bd3449874b56539269116c7e837e1860a6045e1b90a683440d600020efc034a188cb6453f267118c7d63831868a6445a1be0a803780da00020e8e033897f4b1651d25290f479c3681808a6445a1b20a2035c0ce00020e1f034518a0b6e54b26b91807f03811870a7c46a1bf0a683740c800020db1e32d97b0afa50a25190b47983561780a3042c1a209b03480c800020d41d3471874b6a53a262113c7b436b17c0a644581c60a783680da00020cd4d32d1800b1451a25691007b036017c8a4042a1ad0a283780dc00020c66f33d97f8b0651c25991247c237d1850a7045c1bf0a7037c0e400020bf943379808b1e52a26091587a83751818a484501b70a303840e800020b8c633197dcb2452c25e91307b436c1800a684441a909f83700ce00020b1ee33317b8ae850124890bc78a35717489d44161a509883300d400020aadb34c1880b5453125b912c7cc37b1878a604461b10a683680e000020a3d334d18a8b6c54d266118c7ea38d1930acc4881cf0ad83c40fa000209cda3431844b3052b26191207a635c17389e84261a609f83600dc0002096143289790ae850a24d10f07a036517b8a2443c1b209e83480d6000208f0734d98a8b6c544267919c7e83801840a6045a1c00a783780d80002088213421820b2e51f253109c78836217a0a204321a90a483bc0e40002081523349814b2252e266918c7dc3741830a7c4541be0a3036c0e2000207a633381818b3853126011287c23791850a644681c30a7838c0f40002073af3231748ac24f4246107076034216789a840019809d033c0d4000206ce532b17ccb2452425911207b836917d8a1c4201a009b83300d80002065ee33f983cb3052c25d91807dc38018b8a804541c30aa03a80da000205f0f33617f8b3052425b91187a235917f0a184261b40a103700da00020582833817e4b2c51b25511247c836c1838a384481be0a9037c0e800020511c34d18a4b6c54926811847de3761858a804561c00a983940e4000204a293479854b4a53726991847f23851870a984661be0aa83b00ec000204335341182cb3453026391607c837417d0a1843c1b20a5034c0dc000203c5533a182cb5453025e11287ae3701820a604741c90ac837c0e20002035583429848b4653426511707f238b18e0a804541c10a803740d2000202e9832a17a0b0651625110e87b637018089e44261ab09e03440ca0002027ce33397fcb2852a25c90fc7a436617e0a2842e1a709e83680e00002020f43381810b2c53226111347ce3791838a5444e1b50a483480de0002019f33499890b7054626991a07ea38d1910a9c4681be0ac03940f000020133732817a4b0a52225791187a035d1750a244441a909e836c0ce000200c2f34b9894b7254f27191c47ec38618f0a8846e1ce0b203d00f400020057932617b0b1a51525390f87b236717b0a204341b40a303940d60001ffea33399824b3852f26291607c23781868a804561b80a103740ea0001ff7ba33f1860b5e54a26c91787f838a18e0abc47e1d00ad03b81000001ff0e03359808b3e52f26591487d63701810a4c4401b80a603540d60001fea0333c9808b1851f25a11487cc37c18b0a8c46a1c90b083b40f40001fe33333417e8b2051b25990f87ac36e1810a3043e1bd0ab83740ea0001fdc49340983cb4053526011247be3791830a3c42e1b10a503580ec0001fd57633497d8afc51625510e879835f1750a004281aa0a3038c0e80001fceaa32d97dcb1e51c25811187c23781838a7c45c1bc0a783600e20001fc7ce33917d0b08518257111c7bc3701810a6445a1b50a8838c0d20001fc0c63499874b5e54026791747fa38f1888ab04761ce0ad03980e20001fb9f533197c0b0c52025d11487a035e1790a104281ab09e83600d00001fb2eb3471870b42525257910479836017189f841a1a909c03340ca0001fabf43419874b6453e263116c7e637f1868a7845a1ba0a703840e00001fa4f63439860b3a52c26211407b236a17c8a144381b40a203400da0001f9e0833e9824b3c52f25b91747e43831880a884541b40a503700e00001f972533697dcb2652825791247ae35917609fc4241ab0a083400d00001f901f34b1890b5a53c26311647c637c1870a804681b80a583540d40001f894a33217d4b0e51b25611247c036917e0a2443e1b209e83580e20001f827332f17dcb0e51e25a910c79a36417409f842e1a309d83680dc0001f7b6d34a98a0b7254826a917c80c3951900ab446e1bd0a4836c0d80001f749133517f8b0651125110e079635917e8a2041e1a20a203700ea0001f6db43399824b2252c262116c7d43731820a944681cf0b103bc0f60001f66d53389800b3853a263113c7ca3721800a6043a1a809d83480dc0001f5fdc33f984cb4653426211487ce3761868a704481c10a883800ce000 else 0x22cb5e3399818b2852225411247b236b1860a6044c1ba0a283480d400022c47933a9834b3252726311507ce3721808a2c4421ad0a183680e200022bd9d33a1838b3c53526411647ce37a1830a404561be0a883980da00022b6db32c1788b0451b25a11307d03781830a5c4481bd0a403780e600022b0233239798b0e51625310ec7ae36d17e8a3c4401ad0a203680d400022a92e33a1818b3a53225a91287ce3771878a504501c30a7836c0e600022a26932d17c8af650f25110e87a236717c0a3844c1b30a383800d6000229b4c35818d0b8254927391c880a38f1900ac44701c00a9036c0e40002294453499884b5c52f261916c7d43771800a444361b40a7837c0d4000228d61337981cb4c52225d11607ca3751860a584381a60a203640de00022867833b9828b3052d25f115c7ca37917c8a4443e1b40a403640e4000227f8a340183cb3c52d26211607d23721808a4445c1c00aa03780de0002278833479868b5c54226a11887e83841860a804441af0a683a40e200022719f33f984cb4454326811587ca37b1858a4c45a1bb0a603540c6000226ad932b977cae44fa245106c77e3501748a104321bb0aa83880dc00022642b32517b0b0052025b91207be3741808a284521ae0a503800c6000225d4b3329824b2852625891247aa36817b0a284181a109d031c0c800022567333a9864b6054d27311e080838c18e0ab446e1bf0a703700e8000224f9e33a1800b0852625d91187bc3751850a6c44c1b30a303740e400022488235498f0b9655827891f481439518e0a984581c00a7035c0de0002241c232a178cb0e51a25190dc77e3581768a3443e1a109d83600d4000223aec33197ccb1452225811347c236d1808a584301a70a1835c0da00022341333c182cb3c534262114c7de38418f8abc4721cc0ab839c0ea000222d4e32b17a8b1651725090e87963651818a684581bb0a783740cc00022267233a9818b2e52425590cc7a83701810a3c44c1b00a103740dc000221f8033f9818b1e51425090e478834d16e89c841c1a609c03540ca00022189633d1834b4853225c91347b23731878a6c4581bb0a283640d80002211cb33217f4b1a52425b111079836217a8a104201a809d03240e2000220abe34d98b8b8054b26d11b07e43921908aac48c1cd0b103b40f20002203dc33b182cb3e52525e91207b83701858a244501ba0a6837c0d200021fcff33597f8b1e52525490f879e36d1838a644681c40ab03840da00021f64a325978cae450724b10b479235a1770a1042c1ad09c83640d600021ef5933d97f8b2c52a25b91347be36917b0a0c4341b70a3834c0d400021e84c34c98acb8255526c11907d03791818a4843a1ae09e83580d800021e15134b98e4b8e55026e91f081e3971940b0c4a01dd0b003cc0e200021da5e3411850b5654526c91ac7f038e18a8a9c4621c40aa83740d400021d36c33b9804b3e52c25d91407da3791838a6444c1ba09d03340ce00021cc8133b9810b0e51c25591007ac3711850a684581c00a8036c0d000021c5c532a97a8b0052025710e479e36117809fc41e1a90a103600d200021bef43351818b2a52d25c10e079a36c1780a0c4381b20a083380d400021b7fb3471864b3a53426711787e63811888a7844e1b50aa03840e000021b11133b9810b2851a25991247b437517e0a3042c19e09a03280dc00021aa4732c97a4aec50c25090cc78a36017a0a4044a1b70a003700d600021a33335418f4b9855927491c47fe39018b8ab84781cb0ac83b00ec000219c3834498acb6653f265117c7d237a1830a3043e1c40ab83ac0e400021956d32d17d0b1051a258910079c3661778a2843619f09f83580e4000218e6d3451870b6854726691707e23841868a5c46a1c60a983880ee0002187ac32f1798af650925491107ae36417d0a284261b30a803980dc0002180e033317ecb1251925610e87b036a17e8a5c4661be0aa03740d20002179f13411860b4a53926591687d237417e8a484441b50a3836c0d600021731f33297a8af650e25891347e237d1870a5c4581cc0a9038c0e6000216c213489868b6453526791447d037b1838a884641c60a8834c0d000021652234d18dcb8c55327291e080038918c8aa04621c10a603940ec000215e5432e979cb0e50d25090cc79235917a0a404341b80a603900e80002157823391800b1c51f25991307b036b17c0a3843e1a80a483640d200021507e347987cb5a536262917c7f037f1898a884701c70a6035c0da00021499233c97f4b2652d25f91547c43801860a804481ba0a703980e40002142b93341804b1c51b25911287b036117e8a3c4501bf0a5836c0d6000213be73379818b2652e25f91347b03771828a344341af0a183540ce0002134dd34b985cb5c53f26a11787ce37717f8a4844c1ba0a483680e0000212df4342183cb4053526611687d237d1860a744761c10ab03980de00021273232a17b4b0051f25591307ae36217b8a4c45c1c30a803a00f600021205b33597c8b0451024e90f47923631768a084301ac09c83380b600021194d35198a4b70547267119c80438f18e8a944561c10a6837c0d8000) else (if i < 20 then 0x2484083461880b6654726c918c7f43801870a6845c1be0a903800de000247cf33511888b6053f265914c7b236317e0a2c4361a90a3035c0e800024762132f9820b4253226311747d63761840a6844c1b50a283880e2000246f2b3439830b4853125c91487c036817f0a584621c20a7039c0dc0002468793271780afa50725190c078035217289ac40619909a83300dc00024617e3421848b4c535267115c7d437c1810a8c45c1ba0a703840e2000245a9933697fcb1c51f260115c7da3701828a5044a1ae09e83300c40002453ad3421848b3253e26991b47e23771818a8c4601bf0a983600d2000244ce532e17acafa51125810f879c35b1790a004301b70a603700c600024460833617dcb1251324f10e479435a17e0a2c43e1b90a283580d2000243f3133397bcb1050c25010c47983651830a504421b50a5836c0c600024387c3229764ade502248907c7863571770a104341ba0a403840cc00024317f349187cb5054526c91bc7fc3891970b0c4a01d60ab03840f0000242ab13321794ae050b25290bc7863571758a044281ae09a83200c80002423bc33e1838b3452c26191707c636a1830a4443e1ba0a903840e6000241cb634a9894b5e54326a91747d03741868a7c45a1ba0ad83bc0f60002415f033097dcb0e50924f10f07a035917a8a404521b70a183540dc000240ee73471874b5e53725e11687d436917f0a744761c80ae03800f000024080a3389818b2652125f91507d63741868a644621c30a903a00e0000240105347187cb50533269118880039118e8ac048a1d80b103ac0f800023fa08344987cb4e54426511a07ea38818a0a8c4701d00ae03780ce00023f3373369808b2652525b11387ce36f1850a644541b90aa83940de00023ec6333397ccb0e51e25a11307c236d1828a5044e1bd0a983980ec00023e57c33f9858b4e53926911947f839518f8ad44921ce0a983b80ee00023dec333017b8b0051225a11087a636d17f0a404481c10a103680ec00023d8123259754ad24f3242907476434b1750a0c4541b50a503500d200023d10d34c988cb6854026911a47fc38a1820a4c4521b40a2035c0cc00023ca3033b9800b22527261116c7c83761848a704681c00a5837c0d400023c35733a180cb2452c260916c7d038418c8a704401b50a2837c0e200023bc723381828b3652b25f112479835d17589e4416194094830c0c000023b59233997f8b3653125d91487d038418e0a744601c80a8037c0de00023aecf324976cad850524b90c479a35b17689f04401a309d03540ce00023a7f733a97fcb1852325d110c78a35c1788a084161a30a0035c0d400023a0ea34d18a0b7054527091907da37c1848a7045a1ac09d83580ce0002399ee344986cb5e53d267917c7ea38218c8aa44661bc0a303500ca00023931233917f4b1852325d112c7ac3621848a3442e1aa0a0834c0da000238c3733397e0afe51c25791007b036617d8a3444a1b40a603780ee0002385293531898b5e541268117c7f038617e8a404441b50a783640e2000237e4d33f1834b3652825e11147b437017f0a3842e1b20a183640d400023775d3449858b4052f25a11207c637f1840a884501b209c83480d400023706f34798a8b8855827191c880c38b1880a784601c20a783780ec00023696f346987cb6453c26a11647c43751810a6445e1bc0a283800ca00023629533a9824b4a54626a91887d63851898aa84581b60a9038c0f0000235bd432797a0af050724a10cc78a36017489f04281a509c83240c40002354f733797ecb0c51724e10ec79234917289dc41419d09e030c0ba000234e1533d1834b3452825b11147b836917d8a304401ab0a203800e200023473033d9820b2251e256111879635f1790a1c4461ae09f03540d600023406a32e17d8afe50f25210f87be36f1818a304381c30a483580cc00023397a34898acb7654126511647d03781798a084461a809f83380d40002332b432a97c4af251125490e87a636a17e0a2c4441be0a4835c0cc000232bed32997a8aea50f25390d879034e17489cc40819109503080c20002324fa33e981cb4c53025b91287b23731828a8045a1c40a603b80de000231e1f3359800b1a51825a90fc7ae35c1798a284261a709d03680e000023173233b17f4b1452425d91587d638818e8aec4801cd0ae83a40e400023104733617fcb2c53426811847e638318a8a9846c1c50a703740ea0002309643391828b4a54026591747e237e1828a344281a909f036c0e000023029733397c8b0250a25090b477c3511718a104281a50a003400de00022fbc433217e0b1e52125e91307b23711800a4c4561b90a683780de00022f4c93489858b5653925f11447e437e1900acc49a1d60ac037c0d600022edc734598a0b6453a26191547de38618c8ab047e1c30aa037c0e000022e6d23439818b4653625f11507ca3781838a6c4601c10a283680e200022e03231b9738aba4f624910c078e35917509d840818a09302d40bc00022d93034a1888b6254926d11a07f638a1870a9047c1cb0ad03700d800022d24233c1828b2c53826291787c636f1870a884761c60b003d40ea000 else 0x263ab533117c4b1251a25911347c03791830a6445e1bc0a603840d40002634083281794af051125310d478a35a1778a304321a709d83540e8000262d3533417ecb0650925010cc77a34e1770a244541b80a003800da0002626403461884b6653826091607c037d1868a8446c1c80b083c80ea000261f7333117f0b1852226291687c43781858a3c4461b50a303440d200026189633717f4b1e51c25c11447d637717c0a2c4501b60a4036c0de00026119c34a9890b6c54126811807d837b1830a7445c1c10ab03940e8000260ad9323977caf250f25410bc77235317389ec4221ab0a1035c0e20002603fa33617f8b2a52925d91547e63831870a784601c20a703940e600025fd20338180cb2a52925e913c7d638818c8a9c4661bf0a803780e200025f63a336980cb2052825b913c7c037217f0a744681c50aa03980e200025ef813261794af050724f10f07ac35917589ec4261a109f033c0c000025e8d931d1750ab44f2242906477634416d89b04061a009903480dc00025e207337981cb3c53426591747d437e1868a644581c50aa83940e600025db17340983cb5a53c26911b880439318e0aa848e1d50b283d80ea00025d4593261790ae850d25210e47863521748a084301a909c83540e200025cd51346989cb6854126991907ca37c18a0a6c4541b80a7038c0d600025c67d33317f8b1e52425c91187aa35e17c0a3043a1ab09d03440ce00025bf6335118dcb7454526411907e437f1878a5845a1ba0a003780e000025b87f33c181cb3452925810f079635e1808a304381bb0a783900e000025b1ab33717e8b2452526191247b236e17e0a644541bd0a203680de00025aae43271780aee50624d90dc7a03681758a0844e1b50a383580de00025a41f32817a0afa50825210b478235f17909e44101a1098031c0b2000259d63321976cae450f25010bc78a35d17289f04201a709e03540d800025969433597f0b2c52725991287ac3651798a1842c1b20a1035c0d6000258fb23391800b1a51825c91487b43761890aa446c1bf0a583640ca0002588d33381808b1e51825611207bc36c1818a484581c20a603480dc0002581fa3349808b1051d25511107b636217d0a304561b00a183940dc000257b513231768ac04f1241904c76434d17089dc40e1a70a0036c0ce00025745a3461840b4453b26191407a63731868a704661bf0a5836c0d6000256d8b3311810b0c51f25911007a435c17389d841019e09a03340d200025668b3421874b5453a26691887d636e1808a344421c40a503680e4000255f8d3471868b5e53926891b87f038718e8aa44721cc0a883900e80002558a433f1848b1850e25290b477a3511768a104321a309f03280d40002551c93389804b2651d25490f07b436d1818a4c4521b70a083640dc000254aff32b97c8b0e51c25a91107b63731808a6445c1b70a3837c0d400025442e331981cb42530265113c7d63811828a1c4421b30a583800d4000253d5133e1814b3a53826211247c036f1808a6c4621bd0a6038c0f8000253653349188cb6854126811747e038c1930ae047c1cb0aa03600d0000252f7e32f17ccb1652925c112c7bc36817a8a0c42a1aa09c83780ce0002528b132c97d4b0451325590d47a436617d8a2c4341bc0a783680d40002521dd3351808b3052a25e11407ce3871890a9046e1c20a883880d8000251afe334180cb1a52825c11307bc37b1880a744761cb0a383780e200025145a31b9734ac84ee241107c75634116f89b040419409902fc0c0000250d7733b181cb3252f26111407da3731840a884741c90aa035c0ca0002506b532e179caf04f924810ac78c35c17509e84101a009e83300c800024ffd03399800b36524261113c7b637e17f8a544501c00a803780dc00024f9143239780ad050524890a478635316e89983ec19909b033c0c800024f2333379800b2e52425a11407ba3691850a3044a1b40a783a00e800024eb453421840b3052925c912c7bc36d17e8a7c4661c20a703740cc00024e47833297dcb0e51c25090dc7a235d17c8a4443c1a309f03600c600024ddb632b97c4afe51324f10e47b437f1870a6c45a1b60a883680c600024d6cc3411840b3e54326711887d83781868a7445c1b50a103540ca00024cff53351800b3452925c113c7be36c17a8a5c4521be0a7838c0d000024c8d935698f8b9e55727591fc80239018c0ab446c1c40a783780de00024c20033a17fcb2052c25f11247aa36d17d8a4043c1aa09e833c0d000024bb263399814b3453826211607c237a1848a684761c60a903940ca00024b44333b9834b4053926891c880e39d1960ac84801c80a9836c0e600024ad4f3401840b46532261113c7da37e18e8ab044e1b30a203580d000024a67d3379800b1c51825691287b036e1868a844561c00aa83880e2000249fac32e97c8b0651625710f07b837417d0a4845a1be0a283480ca0002498b0346184cb3a531262113c7b63711810a304561b20aa83880da0002491f432897b0aec50924b109c78435e1790a3c43e1a609c03580cc000248b0733f9840b3452325991187b837a1888a804641c30a9838c0ec000)) else (if i < 23 then (if i < 22 then 0x27ef8932e97ccb1e519257911079a3671818a284361b60a483540da00027e8b533117c4b2252e261911c7bc3701830a3443a1ab0a083580dc00027e1d633c1840b5253926211687ca37418a8aa447e1d70b483b80fc00027db0233617acae850325491287ba3691778a3c4481bd0a683c00e600027d43733097ccb0c51125110e87b836b17e8a4445a1b40a183840ea00027cd3834b18a4b6a54826b11a87ea38918c0a8c4541b60a183680e400027c67932917a8aee50d247909c77635817289ec42c1b409f838c0ca00027bfa832f97dcafe50e24d10c87a235a1780a104181ae0a1834c0d200027b8df3309800b2852c25c91247c237017e8a2c43e1b50a383500de00027b23a31c9748abe4f624a109076634c17109c44141a40a003540c800027ab4d33d9824b3653026091087b436d17f8a6043e1b00a003540cc00027a49f320973caca4f924b108c77434e17409f841a1a809e83680da000279df2323977cae64fe245905875c34e1780a2c4421b50a403740e000027972233017dcb0250e25310b87863591798a444421a409a83240c200027903d33e9850b5853c262917c7fc38c18a8a784541c10a603580ce000278963337181cb2852225d11007b03651770a204461b50a603940e000027828433697d8b1852825f91407ca3771858a9846a1c00ab837c0de000277bcc32997c4b1052325410ec7a83711830a5445a1b80aa03680c20002774fe32d17a0ade50c25510e87823551780a404341ac09c036c0d4000276e0c344185cb6653a26c11d080a3811868a6843c1b10a5834c0e000027674033017b0af651725691107b83731838a4c44c1b00a303780ec00027607c32a1788af050d25010cc79035617089ec41c1a209d83540d00002759ac33017acb1451e25d11307bc3711808a744661ca0a8035c0c20002752f1326976caee50c24a90e87aa36717c0a4c43a1af0a383540d8000274c1133c1830b2e51d25711147b037817f0a544481bc0a683840e0000274515348188cb5e53726391787e63801860a484481bf0ad03840e0000273e473389810b2652625990f07a63651820a604481af0a703780ca00027378a3269794afc50f25190f87a035b17189f043a1b70a403680dc0002730b43369828b3e53826791547dc38118c8a8c45c1b20a883740e00002729ed32c17b8b0250b25110d07883511728a004461ab09e032c0cc00027231933097a4aee51a259913c7d637f1838a6c4641bb0a483840e2000271c133489864b4053a26711587be37017e0a504581bc0ab03a00e20002715113471880b5c54526b118c7e238b1930b144ac1de0b403d00f4000270e5a3241790aec50d25310e878c35f1758a184361ad09c83240d200027077233517f8b1c51425310d878c35d1750a1c43c1b60a983900da00027008c3381824b2e52b25f91347be3711868a804661c40a9839c0e400026f9ad33497e8b1c51925990fc79435017509c441a1a009883240cc00026f2cb33417ccb2c52d25d91587d03791818a444521c50a8036c0d400026ebf133417ccb20518254110c7b036817b0a0043c1b80ab03680e200026e53b32a97a0af650924f90b477434b16f09dc42219b09282e80b600026de5a3339804b12522258110079c35b1760a244341b10a3833c0b200026d7b331a9738ac4500245107476a34c17109d841a1a109d03540d600026d0e532a17c4b0851225610e078c35b17009e441219d09c83300dc00026ca2e3229754ade50924e10cc79036317a8a1c4421ba0a6839c0e400026c35133b181cb1e52e25b11247b236d17f0a7045e1c50a603900d800026bc9432d97f4b1c51d25b91207c63711800a344561b80a703900e400026b596348188cb6c53a261914c7d03761890a604441b60a803780c800026aeb133a9840b3e52b25e11847d63721808a184321a90a3038c0e000026a7d63391804b3652426191287ac36717c8a3c43e1ac0a103480e600026a0fd33497d0b1a51e24f90e87b436b17f8a484481b30a0835c0ea000269a1433d1840b4c53f267919c7ee38918c0a844661c60ac83ac0dc00026933b335980cb2a52b260914c7c23731830a5c4441b80a683880d6000268c6f32e177caec50924e90b477c35417709fc41e1a50a0035c0e20002685bd3281784ae04f924310a47783551780a1043c1bb0a503340c8000267f1c31b1714aa44e8246908075c34716d89b43f018b09703400d000026781f34918a8b7e54c26e11a07e638f1908ab84761c20a303880f6000267169329178caf651325311107ae3611738a0c4421bc0a583800ee000266a9733417d8b1451825111007a43631748a084241a509b03440dc0002663aa33f1844b6454b26a917c7ec37f1858a9045e1c30a903840e0000265cd633717e8b0a51225090ac78635617289e441e1af0a303600e000026560c32d17a0b1051c25110ec7a036617d8a6c45a1b90a583600da000264f5332717a0ae850624e90a87863551780a3443a1ab09d831c0ce00026485a3499858b7a54626d91707ea3871898a6c46c1c40a883780ca00026419133317d8b0e51525090d07a03631778a2c4401ba0a7036c0cc000 else 0x29a3d33259760ad04fd24890a076c35017009cc40e19c09883440ca000299d0732a1790af250a24c90c077a34e17309d04041a409d03340c400029964532b17f8b14516257111c7ae36a17b0a4c4541be0ab83d0102000298f8332d97b4b0851a25890c878235f1778a0041c1ae09c03500d00002988c0328978cb0051425991447c23741838a604421b709e03380d40002981a735398dcb7e54d26911647c23781860a744641c50a783700d2000297af13261778aee51325710fc7a036417f8a384241a409e83400d600029741e335979caf851125b11047ba35e17989f84321b70a703700e2000296d4033e1834b4453726591887ec37c18b0a784541b90a603640ca00029667832c17b4b1051625811187a435f1790a2c43a1b20a583600dc000295fb832c17b8afc51924f10f078e35517209f441e1aa09b833c0d40002958cc3421844b5a53d26191487c437c18a8a744641c60a683580dc00029522431d975cae24fe24890707623411730a184281a10a483700ea000294b6c3211750ad04fe24b90ac7883511728a0c4301a90a083480ce00029448d33817fcb1451d25a11487c43721858a9846e1c50af839c0e2000293da533a184cb3c51a25a11387ba3751880a644581bb0a983740e60002936d632f97c4b1a51325891147be3771850a4443c1ab0a383780e6000292fec33f17f4b1651e25c11087ac36917889fc4281a809883340d00002929163369840b5254226391587d637a1860a7446c1c50a883900e200029225b32917a4b0452425c11187c238518b8a6c45a1b40a5035c0e2000291b5d3461868b4a53e26a11787ea3801848a544621c00ab83a00f2000291483334180cb2c52625610fc7aa36317d8a384521bd0a1833c0de000290dab33b9844b3c52d25f91207b037d1818a604621c70a383740ce0002906f632417acae650424f10bc76834c16f89a84161ad0a283540e400029002333697dcb2a52025c91047b836b1798a5044e1bc0a3034c0da00028f96132917a8aea50324b10c878035016f89dc42a1a809f034c0d400028f2713419838b2652025611087a236517a8a244421ac09d83500da00028ebb7323175caee50c25410e078835817b0a344341b40a8836c0da00028e4de33417c8b1051d25211207a63711820a6045c1bd0a883940ec00028de343209750ae050624f90cc78435e1798a3844e1af0a103500de00028d72e34d18a0b7e55627191d07fa38e18c8a9846a1c80ad839c0d400028d05e32d979caf0516255911c79a35817889f443a1b00a403780de00028c99b32e17b8af851025410e879836b17e8a5446e1c90a803840ea00028c2b533f1834b2e52d25a11307ae36d1838a744561c20a8837c0e200028bbeb33117ccb00520259913c7a836817b0a1c4381a709d034c0d600028b52b3289788af650724d10ac78435017209f042e1b50a4833c0dc00028ae863199734abe4fa246106476034616c89a03fe19d09e833c0be00028a7b233097b8b1e51925310dc7943591800a444341af099832c0d200028a0d0337980cb1a52525d911c79836617809e441e19c09d835c0d0000289a173299768af250324f10e078035217689d84221b30a383640d200028931f348987cb5c53926511747de37c18a8a8c4601c40b103cc0ee000288c0535318b8b8e55526e919c7fa38c18f0ab04701c90a903940ea0002885533241794af050f25410f87963521760a204341b009e83280e0000287eae31c1750ac050224c90c077c35117089e040e19409a03500e20002877cf3389808b1651b25110b878835317e0a084421b40a303780e40002870ee33a97e4b2052025b91007963611758a1043e1ad0a083480e2000286a343259764af651625610ec7a23671800a144221aa09c83400d600028636133597dcb0250f25710fc7b036017389f441619f09483140c6000285c8d33217f8b32520258910c7a436517c0a2c4361b10a503500ce0002855cb32617b0ade500249109077a3581778a2043e1a609f836c0e6000284f153239760acc4f8244106c76434116b89e440219d09e83600de00028485032d1798aee51225290d078c35d17c8a504441bd0ab03640cc0002841a03221754ac44fb24c109877635917d0a184481b309d034c0ca000283ace3331818b3253525e112c7d037c18b8a8c45e1be0a9837c0e20002833dc3441858b3e53426991687d237c1818a7045a1bb0a883980e2000282d0833317e4b1a51d25790fc7ba3721858a844781c50a8037c0ec00028261f33b1838b3852d25c91207c236517f0a2043a1b10a603940da000281f3f33a9848b3e53226711847d838518d0ac44841c90ac03940d600028186d32e97acb0051b25811507cc3721828a584461b40a1033c0de0002811983349810b2052225c91287c836b1830a6045e1c20aa039c0ea000280abf33517c8b1e51d25b11287d038b18f0a904701c50ad838c0d60002803e03351800b0e51a25910f47ae36917b8a144381b80ab83980e800027fd0133c9828b4e53a25f91307d437017f8a7045c1be0b003a80f000027f653325175cae650a24d10a477c35717409e442a1ab0a0035c0c8000) else (if i < 24 then 0x2b577633317ccb0851125610f07a236017889fc4241a70a383680ec0002b50843421874b5453c26a917c7ea38918d8a984781d40ae83a80f20002b49bc32f17b4b1452a25f913c7ce3751810a244281a709c83500c60002b43103211728aae4f1247105875c340163899040c19709a03100ca0002b3c633239744aca50024a909477c35617b8a4c4581bc0a5036c0e00002b35b03229780af050024c90a878235016d89ec42c1a309e034c0d80002b2eb933c1814b1452325c11387c43791808a5045c1c90ab03940dc0002b280a32217a0afa50a25190cc79636817c8a284381b40a203800e60002b21543251748ace4fa245107876634a17209c041e1af09c83500d00002b1a6a33f9838b4852b26111387bc36d17b8a084141a409c03340d40002b139133397e0b0c51225710f07a236617a8a4844c1bc0a583880e20002b0cd432d17c0b1652025791087a63691810a7444a1af0a683580e60002b060433017e4b1e52525b11307b036b17e0a4c43a1ae0a083500cc0002aff2c3361808b3a521256110c7a435a17709f843a1bb0a0837c0e40002af85f32f97b8b2a51125310d47943601750a204301ac0a183480cc0002af1a9326978cb0252025391047c83671820a6444a1b70a2036c0de0002aead233097d0b1e52225a110c7c23761818a4844c1b60a603980d80002ae40632d17c4b0050824e90e479e36b17e8a5c4521b40a403640da0002add193401864b4053d268117c7d43721888a6c4601ca0ae03b80f00002ad64432c97bcb0a51225110f87b837417f0a2044e1b209d03700dc0002acf943249788ade505249108475a34316f09d84261b10a403540d80002ac8d532817a0aea507248108877635617a8a3c4421aa0a603780d80002ac1e833717e8b0a51525490fc79636f17c8a244381af0a003300c40002abb1b32f17b0af2508249109878835217389e84181a309a83200c00002ab45532d97c8b1251825190d479e36817f8a544461bb0a4837c0e60002aad8932d97a0afe51825090e479e35f1758a004381b70a203600d60002aa6c332a97b4b0c51a25790e47b035d17509e841e19e09903280c60002a9feb339183cb0e51b25411007b63771838a584501b80a783780e20002a99053399808b2052a264915c7e237d1810a584601c20a703840e80002a926c3189728ac04f4242907878234f1720a044461b40a783600d40002a8ba532b17c0afa51725411007a835c1788a1c44e1bc0a603900e20002a84e432e97d0b0c51725710d47983651808a5c4521be0ab038c0e40002a7e023351804afe50f24d90e479c36c1838a7446c1c70a4838c0e00002a773832e17b0ae850f25390f079835e1798a1c4561bb0a7035c0c20002a708a31e9744aca4fb249109876c35b1798a244281a309983540d80002a69cd3261790aec50e25010f87a836417d8a0843c1b70a4036c0f00002a62fd33697ecb1651e258111c7be37317d8a1c43e1b50a803800dc0002a5c3b3291780ad84f9248107476835017589fc4281a809f83380ca0002a55463429844b4a53425f91707da38418a8a8c4721c20ab03a81040002a4eae3121718a9e4ed245107c76e34516f09ec4201b00a503740f00002a47eb32e17b0af650f25710fc7983641790a204261a709e835c0e80002a40f63419854b3253226311547d03751858a7845c1c20ad03940ec0002a3a1733197c8b0e52025610f07ae35d17c8a504521b50a1834c0dc0002a33253411854b3452f25f91747cc37e1898aa04661b90a583800ea0002a2c6132e97dcb30527257111c7d638618a8a7c4601c50ac83b00dc0002a25e430c96d0abe4fb24690ac77234f1738a1c4321b10a383500dc0002a1eeb3491858b6054426b91847e638818c8a9046e1c50aa83880d60002a182532a9780adc4fb24f90c477c35617d8a1c4341b20a3837c0e00002a115533097b4afc51825711207a636317d8a404541bc0a4837c0dc0002a0a853371820b2c523255110c7b035e1780a304541bd0a403780da0002a03d13291798ae250725410bc79036017989f04161a90a083280d600029fce833c1800b1a52225c10fc7ac3611808a4445a1c30aa03980dc00029f60033b9814b2052525790f079a36817a8a284541bc0a603800d400029ef2f3319808b3052a26491907f638e1910aac4781ca0b103c40e200029e85f3361814b2051a256110c7be3651808a5843e1bd0a203640c400029e19e32a97a0af251d25d91307c63781880ab446c1d20af83a40fc00029daa5342188cb7a54826991887e638518b0a884601bf0a703a00d400029d3e63229768ad84eb248909476034c17189e03fc19709c034c0d000029cd1a32e17c0af050725090dc7883581798a2443c1b90a8039c0cc00029c62d345188cb5c546268917c80038d1900aac4781c90ae83880d800029bf473389814b3053326891c480639118f0a9846e1c40af83bc0f800029b85b33b982cb3853025f91487ce38918c0aac47a1ce0ad03940ea00029b18733797ecb2052125710f07a436317e0a584561b80a883780e800029aa8b3489890b6654926a117c80039218e0ab047c1c70ad83b00f4000 else (if i < 25 then 0x2d08d3326177cae450824d10bc78435917409dc4241a909b03480d20002d020b32c1790b0650b25711007a43671820a484501b40a283680d20002cfb4e32897a4adc4f6246107477034b17209f04241a60a003600d80002cf46133b9840b4052325e11407c83771808a484621c20a683640ce0002cedbe31b976caea51025290ac76e35c1760a284261a309e83440ca0002ce70a32b178cae850a24e90c078a35217089dc4241a309d03480d40002ce0353341808b3051b25390d47a636e17e0a8045c1b70a203640e40002cd96a32997d0af850824d10c879235c1778a2843e1b80a1833c0c20002cd29d33097d8b1c52725a91607ca37618c8a844701c20aa83ac0f20002ccbe132d97a4b00511253109c7843541760a0c4381ac09e83540d00002cc5093399844b4453726491887de38c18d0aa448a1ce0b183b00f00002cbe1f33e9820b28523257911c7b036f1820a4844e1c30a8036c0d40002cb7703201754ad24f6243907076634e17389cc4181ab09a032c0ba0002cb0c53219750ae050624e11047a835b1770a084361a909e83740d60002caa113241798aee51525390c078a35617b8a4c4441b90a3035c0e60002ca35132d17a4af851225290d87803631790a2c44a1b70a783840e00002c9c9f32196e0aa44e1236901873233b166899440819909683080c00002c95c533597ecb1c52b25b113c7be3761858a5846a1c50ab03b40ec0002c8ee533d9870b4c53326211407ba3731878a6045a1b90a3836c0e20002c88553191720aa64ec242105c75e35317a0a244301a90a203640c80002c818133197f0b2652626591947ea37e1868a5c43e1bb0a383740ee0002c7a9f3391814b2a51525c913c7c236b17f8a2c42c1a409d83400e00002c73d033317e0b1651f257910c79a35a17189f04361b60a183500da0002c6d2e31c1708ab84ee243906077235a1760a0c4381bc0a383400cc0002c665f33097f0b2652b26091447be36b17f0a444521bf0a783700d80002c5fa33249774ada4ff246108076e34b17309d04301ac0a483680e00002c58d13379808b2651c25910fc7a636717d8a3c42a1a80a103480de0002c51f7338980cb2651d25490f47a636917c8a384421ac0a183600d60002c4b1d3371818b3253025f11287be37a1820a604561b80a4035c0d00002c445133317f4b0250b25291107b03651820a2c44a1b40a283700d40002c3dba3171734aca50325210f07b036a1788a1043c1b50a703600e80002c3700323976cac850024b909c77834a1758a244581b10a203340e40002c303b3261758adc50524a10c478e35c17b0a244301b90a683880da0002c297132f17ecb12516251110c7a635e1788a2042e1b40a283540e00002c228633b9844b2a53126391407ae3721820a5444a1b80a003600de0002c1be631a1734ac0500245907c76c34b1730a004381ad0a283380f20002c152333097e8b1652225e11447d43811838a8445a1c90a9838c0de0002c0e6233397ccb0050f25210d87a836b1848a5843a1b209f03280d20002c07b132b97acb0a51625711407ba36d17e0a5444c1b60aa83940d40002c01093201744adc4fb24890ac77235717189d44201ab09e83240d40002bfa4e325176cae650124c90d479035f1720a084221ac09e03600ec0002bf3713399800b2852a26591a47e23771840a484521b40a0832c0cc0002bec8633c1840b3c52525e11207b237017f8a744421b30a483440c80002be5ad33c983cb5053426011247c23701840a6c45a1c60ad03880d20002bdf0231e1774ada4fb24910847723601768a2443419509883040d40002bd83832b1774ad650124890b078a35217289f041819e09c83740da0002bd17532e17a4afe51a25390fc78e35917109fc41e19609682e00b40002bca9533f1808b1e52726391547d63781860a8046c1bf0a903880dc0002bc3f131a9750adc4fa24810a076c35416d89e04321b20a383780e20002bbd4632517a8aee50d251110478c35c1780a044141a509d83480da0002bb67e3279784b1451325390d879035a1788a344421a80a083340c80002bafc6322977cae450924f10bc77c3571780a144301b009f033c0c80002ba8e733917f4b1c52a25e91647ce37618a0ab04701bf0a5034c0de0002ba22832e97d0b0c51525911047b836b17c8a4845c1bd0a403780d80002b9b3833a1834b4252525e91407d43751868a484261ac0a003340dc0002b949a3181728ac44f2241905874e34217389f042219809683080bc0002b8dd3325978caf050f24f90a077a36117e0a2442a1a409b837c0d80002b86f43301808b2e53a26311707d03741808a5445e1c10aa83a80e40002b804c3189710ac24f723f105075034d17089ac4161a909c032c0ca0002b797932f17d0b1453325d911c7bc36d17c0a3c4461bd0a7837c0d20002b72af32a97c0af250f24c10a077c3521778a044361a809d83540d40002b6bcb33c9818b2451c25490b07823611778a004281a90a303540dc0002b652131f9774ad04fd246109c75e34817009e84221a209903280ce0002b5e4c3351810b3e52d25f11247c03701808a644521b009e035c0d2000 else 0x2eba493411854b4053d265113c7cc36f1848a644601c20a703880ee0002eb38e32b97ccb2652225991207aa36617b8a504381aa0a583680da0002eace3326977cada4fe254910079e35f1808a4c44e1b60a583680e00002ea63f3229758ad850624d90f87ae36617b0a3c44e1ac0a483700f00002e9f7d327175cac650024810bc76834216e89f041c1a30a003700e20002e98ca3239744ad0501249109876835917309f84261a40a383940f40002e92113271784af451b25290fc7a83701808a7446a1be0a803640c80002e8b7531816fcaae4f124310b878235817209f04341a609a83380d60002e84a63379808b2c51c25291147c036a17e8a144441b80a4835c0cc0002e7dc9333983cb4853025991207ac3771808a604401a609c83380c60002e7701326977cadc50424f11047b836d1840a684601c60a903800f40002e704732917acb0451725791087a036a17f0a4c44e1b20a2835c0d60002e694e3411834b3a52d25c11387c23741820a4444e1b80a1834c0ba0002e629b32897a8afa51025411287ca36f1820a744501be0aa836c0d40002e5be0327178cb0a51925190fc7a435f17589f04341af09e83380ca0002e552832497a8af250f25310e479a36017c0a004221a70a003600d20002e4e6b32d17c0b0451325190c879635b17489e843c1b30a2835c0dc0002e47ac32c17ccaee51325210cc78c35c1780a004241a70a083440d20002e40cd3341808b3c52725c110479235a17709fc4301a709f034c0da0002e39ee33a983cb4a53326311287c43701800a6c4501b50a683780e40002e333132f17d0b0c51325810fc79835a17c0a1042a1b10a2037c0d20002e2c6932e17d4afe50c25290d07a035917a0a244381a80a383580cc0002e258e33617f4b2852825790fc79c36917b8a144361af0a6835c0de0002e1eee31d1750aca4f924a10c079435d1768a1c42c1a40a083480d80002e18443219734ad84fb24c109c76c34616c09e04221a409783580d40002e11693399800b2252625f11447c83771828a404381b70a5039c0e40002e0a8233b9834b4e53326111407d237c1888a8845a1ba0aa03940d80002e03ba3331804b2452725e91307b635f1788a1c4461b80a603600dc0002dfd18319973cad850625011047b435f17d8a4044c1b20a003480cc0002df64333217c4b0451b25410d87a63681800a5843e1b209b03680d20002def923239754ace50324990a478435a17b8a444381ae0a103500d80002de8ee3219750ae050c249109478434916b09d44241aa09e83480da0002de20733e1820b3a52225b11087a836f17e0a484401b00a483800dc0002ddb3632f17acafe52625010c479035817e8a6c44c1b70a503ac0fc0002dd47432897a0af650a24810cc79c3641838a744561bd0a483580c60002dcdc231f9788af4517253112c7a836a17f8a284301a70a203340cc0002dc72031a970cac64fd24990d077234e17389fc42a1b70a7837c0e00002dc04633617f0b18519254910078e35a1788a2842a1a40a383340d40002db9933209774ae250c25290ec7a835e17709f041c19b09c83380d60002db2c033717e0b0c52c25791247b63671820a6c4761cd0a783700e20002dabf4328978caf050824f10d877e3521740a004221a209c03400d00002da50933e1858b4053626191347ba36117a0a144481b80a783980da0002d9e5d31d1738ae451025791107a836e1848a4042c1aa0a103600dc0002d979a32f17acb0451524f10d07923631788a084281ad0a1836c0d60002d90c133717f8b3253226611707ca3741830a584301b20a283580ee0002d8a023279784ae651124e10fc79036817f0a2c4441ab09e03480d80002d833c32d97f4b22522255110c7b03711810a7c4541bf0a683600f00002d7c89326179cb1451925610f47aa36617c0a1c4221a409f833c0d60002d75cf3279794af651625810f07a236717d0a4044a1b60a183440d60002d6eee33417fcb3851d25c913c7d437b1848a744541b90ab039c0e40002d680c33b9818b1c52725811247ba36f17f0a3843a1aa09d03480dc0002d61513231794aea51024f10c47723591770a184301b40a183740de0002d5a7633997f8b3852a25d11007a636517f0a504541bb0a7837c0e20002d5383342183cb4a53626591587b63601768a1c4461c00a9038c0ee0002d4cda31e975cae450524e10a876c35d1758a004321b109c83640cc0002d45fa33697ecb2052725691007ba36a17c0a2843a1a80a203981040002d3f2832f17bcb0a51c25811087a036617d0a104401a70a4836c0ea0002d384a32f17d8b2e52d26191547b636e1800a244381ad0a1038c0e20002d31723341810b3653326491447bc36917f8a6c4621b90a4838c0e80002d2ad331d9760aea51225310d879035b1758a0c4261aa09e03640d00002d23f933797e0b0e52726091407b63691820a704681cb0ae83b80d00002d1d58321178cafa51124b90b479435c1760a0c42e1a2099834c0c40002d164934f98a0b6055026a916c7dc37c18a8a844641c00a403740e20002d0f8932a1788af650525290dc7ae36f1800a3c4401b90a883780d2000)))) else (if i < 30 then (if i < 28 then (if i < 27 then 0x306ac032a17bcb0451124f909076834f17109ec42a1a80a2837c0dc0003063f532d97c0b0252025990fc79c35e17b8a044301b20a203280c0000305d593199724ac64f223f103074234416989d440219809783300d200030567733297f8b1851625110d079e36217b09e44221a80a6838c0d6000304fce31a173cabe4fd24c109875e34e1728a004301bb0a583880da00030490233017bcb0c52325310ec7b63711820a5044c1b30ab83900dc0003042543219760ad450125010d87a035b1780a044321aa0a303540d2000303b8932f17acaee501244909c77835317509f841619e09d032c0c80003034bc33497fcb2852b25991387ce3751820a4c44c1b40a883840f0000302dfb32b97bcafc51325791247b43691790a3445a1c30af83d00e600030273532c17dcb1051925590c477234b17409fc4201ae0a5035c0ca0003020823241764adc4ff24b90bc78a35517689e84221a90a383740dc0003019bc3291770adc50624d10c07a235a17a0a0c4201a80a1838c0e00003013063229784af050a24b90c878c3601780a3c44a1b30a6038c0de000300c333391840b6854326c11ac7e438b1858a944661c60a603640ca00030056533217b8b1852a25c10e878e35a1748a104401ae0a383640cc0002ffeba31e1750ada4f8241105c75233e17089f041019a09703380d20002ff7ea33417e8b0651d25990e47943581718a2043e1b30a0835c0c40002ff13d3209748ace50224810a077c35417b0a0c42c1af0a203640cc0002fea7b32f17e8b0451524c90cc7743561768a104281ad0a483640e40002fe3c0328178cb0051525511007a836e17e8a184461b70a9037c0e00002fdd11321972cac24ee242906477635917e0a4844e1b80a083480c80002fd63f33517e8b1c52225c91347c03731888a9046a1c00aa037c0e00002fcf6f338980cb2e53826311547da37d1840a3c4461b70a483940ee0002fc8ab32b1788ae450924c90c079236f17f0a684481ba0a4836c0c20002fc1f7323175cad44f8243907076a34f17189e842c1b70a303500c80002fbb4a3209798afa51425610f47be36e17f0a784401c10a103580d60002fb49c3239794adc50024810c479036817c8a244461ac0a3837c0f60002faded31e9758ac84f6243109078035217309ac4081a5099034c0c80002fa70d33597e0b2c52d25c11407c637a17e0a1c42e1aa09f83500bc0002fa072316975caf450024f90d078835b17789e04301a8098033c0c60002f99ce31d1750ab64f6242105875033d166099c3f418f09083180c20002f93063301798b0450a24f90b87783561758a0442a1bb0a4838c0d60002f8c193401840b3852a25c111c7b63711808a8445e1ba0a303600d80002f855432d97b8b0e50d25690f87a636b17f0a684441c20a803640ee0002f7ea631f9770b04512255911c7ac3611750a2c4341ad0a483580e00002f77e033197d8b1051725811007a236d17d8a8445a1c00a883780e80002f711a32997ccb1652325891087aa36d1800a6446c1c50a8037c0f00002f6a7531e9724abe4ec245108477434717309dc41419e09d033c0c80002f63ae32f17c0b0651524d90d877e35017309e442a1b00a703740f00002f5cea32f17e0b2652625d11447e03791818a184341b80a783a40da0002f55f63419864b4253025f916c7d43791878a704601c00ab837c0de0002f4f2b32e17d0b0a50e25510ec79236617f0a384321ac09a83540d40002f484233d983cb4e53c26511787ea3871880a884661c80a8038c0de0002f418d3251780aea50e24e10ac77a3591798a284401b20a5836c0d60002f3adc3271790ad84fb246106c75c34e17289f84301ab0a583440c40002f343031f1764ada50324e10b077e35b1798a004381ac0a183580e00002f2d8531b16f0ac44fd24d90e47a036417e0a2c44e1b60a703780e00002f26c832a97b8b0651525190b078035217109f04301ad09e03640e60002f1fd733b9850b5254526291407c236217b8a2843a1ad09f036c0d60002f191d32a977cad250325291087b437017f8a4c43c1b30a183440d60002f123833717f4b3a52925e11187ba36d17e0a5c4521ac09f03700cc0002f0b9e31796f4ab84ec240104073c32c16189783fa18608e03040ce0002f04f431a9738ac04f123f904876e35017289e842e1b60ab03800e00002efe3232a17a8ade50724f90d478e3621790a0442e1b30a483700ca0002ef74233f184cb4c540263112c7b836e17d0a1c4301a50a1834c0c80002ef06033a97d4b0c51a25a91247ba35f17c8a184461ab0a483240da0002ee99933117f8b2e52b258111c7a836017a0a444401b30a2033c0cc0002ee2f7321974cad2506249908476434b1770a2c4441a70a203580cc0002edc2632f17e4b1851c25a11187be36c17d8a4844a1b60a7836c0ea0002ed55433697e4b1e51f25710e477635117b0a544581c50ac839c0f00002ece9b32d17c4b1a51725891147983661798a1044e1bc0a383680d00002ec7e13251750ad450024e90f479a36317f8a344421b20a483740dc0002ec13d31c1744ad04fd24e10c478a36017a8a1c4521b80a5037c0e6000 else 0x32195b32d1798b0251325a111c7c036a17c8a2c4341ba0a603880e400032129932897a8af450d25290e478a3561758a2c4421b109f83200de000320be03259790aec50a247906c76c34d1750a004201a509c833c0d40003204de3451864b5c53d261914c7d237517c8a3842c1a009703580da00031fe3332517a0b0c51625511087b036417c8a144321af0a283580d400031f7c82ff1694a604cd2330fbc71c33516789803e418c09403180c800031f11431f9748acc4f423f102873833616f09bc40c1a609c03380cc00031ea5d3229760ad450324a10d478236017c0a244341ad0a183680d200031e39c32c9778af050824c10c479236617c8a604541b70a803800de00031dce33221744abc4ed245908877c34a17589dc4141ac09e03640c800031d63032717a8afa51224b908877435a1780a1041c1a709f03800e200031cfa231396d8aac4e323d905074c33816a89bc40019f09f034c0c000031c8d532c17b0ae250a25810fc7bc3721790a3846a1c60a9036c0d000031c20833717dcb2651f260913c7c236c17f0a4c44a1b409e03200d600031bb2933717ecb0c51625991187c23691840a844761d10ab83a00f400031b4783251768ace4ee246106075234017009e84181a109c83680e200031ada933297ccb2852125910e47ba36a1838a8846a1c70af03d00f600031a6e332897e0b1451725410dc79835e17489f041a19c09903240b800031a03431f1740ace50324a90b079c35d17909fc41e1a009a83400d800031998031e9748aca4f5248108c7743561798a184301b50a683900d60003192bf32c1794ae650424a909c77c3581760a0441e1b40a483680da000318c323149730abe4ea23c102473a33416389883ec19309983480c60003185843221750abe50024a909c77235317209ac4061a609f83440d2000317ea633f1854b52532263913c7c83771860a6c45c1c20ab83680dc0003177f731d9744ad650625111087a636717f8a5043c1b80a4835c0d800031712d32a97b8b1651925a91487c436c17e8a544361a90a183400d8000316a7b3229798afc51024e10ec78c36117a0a1042e1ad0a203780d80003163df318972cad450924b909877634f1788a504561be0a683840e0000315d5630d96ecab64dd238901073433416609a840019909983440be00031568633317ecb0251525611347b236117b0a384501b20a703ac0da000314fe331e9738ac04f8242105c75a33a16709ac40819409783140cc0003148fd33797f8b3c52725b90f479e35c17b0a1042c1af0a403540e600031423e3271790aee51925290fc7bc36a17c0a3044a1b60a983c80ec000313b9731d9728abc4fd24990c079a36117609f04241a309a03500d40003134d232f17a0b0c51425690f47bc3791840a7c4581c20af03a80e6000312dfc33517ecb2652c26111547c23641868a5c4581b70a283600d200031275e3181704ab84ff247908875433f17089e042e1b40a583580d800031205d3451860b5e54727091dc81438d1900ad04761cd0b683f00fc0003119ae32a97a4af450524990c47803521778a144381b709f83640d800031130e31216f0a9e4e9240106876834216c89ac4101a40a283380cc000310c61320978caf251525590f478034b17089b442a1a2099834c0c00003105a132a1794afa501249907477835d1788a304301a90a283580d400030fee432a9784ae250d25411287b036b1810a384401ab0a0837c0de00030f81c33417d0af650e24d90d478034f17189ec42a1ac0a103280c000030f1683249788ad850424e10c479835f1830a6c46a1c60af83940e000030ea713419868b5c543266915c7c437b18c8a8c45c1c00ab83b00e400030e3d03191730ace4f4245909877834c1740a0843c1af0a3038c0e200030dd2331f9780aea50a24f90d478235717389e44241a309e034c0d400030d6873181728ac24fe24a107876834e17109ec4301a409c03440d800030cfc73261764ad050425010c479435517a0a384361b30a883940e600030c90e32c17b4b0650624c10dc78236117c8a304341b40a403540d800030c28930e16d4aaa4ee240105074433a167898440a19909983080cc00030bbc2327177cae650924a90d079835e17c8a444521b60a903800d000030b4fb32b179caf051225410f879a36d1820a304421b10a303880dc00030ae7830d168ca6a4d5238100473232e164099840c1a009b83340d200030a79e33397ecb2652225f91507c237d1820a6c44c1ba0a503600d600030a0df334980cb3852925d112c7aa36d1838a6046a1c20aa039c0ea000309a0b33597fcb1051f25890fc78e3561788a1c4401bf0a583980e600030933b33097c8b1a52325e91307b236017c0a3042c1a909e833c0d0000308c7932d97a0b1653026491907d836a17c8a0842e1a509b83480cc0003085e730e96a8a8c4ce239100474834117089e440c19f09903400dc000307ef83411830b3e52f26511607d438518a8a9c4661c20ac03740e6000307836328978cafc51d25510cc79a35a1740a1041a1ab0a203840e400030718b3231760ade50d25110e87a236317c0a204401ad0a0033c0c2000) else (if i < 29 then 0x33c83f33717fcb4052b26191547ca3811830a7c46a1c90a403980e400033c1c630796c0a864db23d904874e33816f89cc41619a09383080b200033bafb32e17ccb2652a25f91207c036817d0a284201a709f03400d400033b43533117e0b0051325691087aa36217e0a344581bd0a8837c0dc00033ad923141734a984da23b1030748340168099c40018c09883040d200033a6f03139720abc4ec244906877234f1758a1843c1ac0a3836c0e600033a03033017bcb0451825a10e47ac36317d0a3c4321bb0a8835c0d000033997032997b4af6511254910079c35817a8a004481ae0a0835c0d00003392c031c9734ab64e9241905474a335167097c40419309983240be000338bdc33d17ecafa51925c90fc7ac36d1818a6445e1cb0a8838c0e40003384ed34a189cb6e53c266918480238518b0a684581c40ab03740de000337e1b33217ecb1c52225991047a836f1818a584401ba0a483700e4000337769323174cac04fd243108075634b16a89c84121a309e834c0d400033709033c9838b4e535265116c7d437c1850a2c4281a80a103640ec0003369d332c17c8b0451625190f87b436b1850a704721c90ab039c0ec0003363253249768ade501249908c7723551778a3442e1a209f03380d0000335c753211728aba4fa244107c77634c16f89d04181a80a183280be0003355943371810b3c53b25c91207aa36a17f0a5846e1ce0b083b00de000334f033189714ad44f3249908077c35b1798a044301b00a283980e40003348753139708aba4f1246907475e3501718a1c4161a00a003740dc0003341d131d1750abe4f1242908877635517409dc4141ad0a003480d6000333b173261794af051125690f079836317c8a4c44c1b60a2837c0e40003334793181718ab44ea23e105475c33d16f09d04061a609a83300c6000332db93291768ae650f24f10dc79235817a8a504381b10a003500de0003326f132d17b8b1e51f25b11107a436017309ec4161a209e83640c4000332055321177caf051325190c07a236417a8a304401b60a103580cc0003319ad31d1738ac84fa24590a078635e17f0a2444c1b00a083600e20003312be3411844b3053326991747e03761820a444421bf0a683880ee000330bf532e97a8af451725891407d03741860a8c4481b80a603a00ea00033051e33a9820b2852d261914c7c437b1860a6c45e1bc0aa83840da00032fe4c335981cb3853225c914c7da37a1870a8044e1b30a6037c0d800032f791325976cae04fb24b10a878035317389d841e1a809f03680d200032f0e232397b8b1850e24e10d87963521710a0842e1a709b83500dc00032ea0a33a1814b3c52c26011487ba36e17d8a3843a1b60a883880e200032e3503221760ae4501248107c78e3531750a0c44e1b60a4836c0d600032dcae31e174cad850424e90f079635b17409fc4481b90a0033c0cc00032d60931c1748ad250324f108877c35a17009e041419e09f833c0ca00032cf5d3239744aac4f424810907743531758a244381b209f03540d000032c89c32d17acb0251724e10b877e3591758a244401be0a383740ca00032c1e931e172cac64f824790b476633c16889c440e1a0094032c0d000032bb243351830b40531263115c7c23731820a404521b50a6037c0d400032b43f33a1804b24529262114c7c43821828a5c45a1c60af03b80ea00032ad8132c17d4b1251625711107a036717d8a444541be0a203600e200032a6ac33297fcb1a52225e11447b83711830a4c44c1bc0a783540d0000329ffb3221768ad24fb24910bc78836217a8a0c42c1a609c83480cc00032991c33517fcb22523259111c7b63641808a6446a1ba0a683780ca0003292733229740ad0503248109877c35217389f84361bc0a683600d6000328bc331f1710abe4e623d103c74a34116e89c040419a09b03400e800032851331e973caba4f2244907075035017409fc42e1b20a583600e4000327e6c3189728ad650424e10c879e36217b0a1c44a1b80a2835c0e40003277bc323974cad250724f909c76a34f1768a3043e1b10a183640d60003270f832c17b8b0651025490f07b236317c0a2442c1a809f03640c6000326a473239730ace4f3245108077234e17109e842619a09783340c400032637e32b978cada504250109876c34e1730a1441e1a70a103700dc000325ccf323175cae64f7244907876634e16f09cc4161a90a3839c0dc0003255f933397ccb0651a25811207c236c17b0a284281a209a83280d2000324f513201738ae050324a90cc78635c1760a3c44e1ba0a583580d60003248b2319973cad050824890b078036217e0a284421a809e837c0e20003241da3391830b2252225910f479036317a8a304401b30a883740f0000323b1f326179caf850524e90d87aa3681798a084321b40a703ac0e200032348131a1734ac050124910a878c35a17989f441c19e095031c0ce000322ddc31c1740aca4f323f105875633516509783ec19109883300d400032270933097dcb0e52426211047a836b1858a6044e1b30a403940ee00032202433d1848b5253026211407d43791850a604421ba0a403740d2000 else 0x3576253191720aa64e523c901474e33a16a89b440619f09d83280c2000356f8931a9744ae650825310e079435917b8a2c4321aa0a283680de0003568c83251724ad250a24d90c87a03681798a404441b40ac03940da00035620c3299798aea51425510fc7ae36f1858a584501b90a883640d6000355b7731a9724aae4e9240104c74c34516a89d84241ad0a283540ce00035548833a1824b3653b26491487be3721820a5c4401b10a083480dc000354db733097b4af051225110ec7b63741848a384461a60a203580c60003546ee32e97ccb2252526011547d237b1840a644581be0ab036c0de00035402c33217d0b1e52225c910c7aa36b17f0a604381b00a2834c0cc000353981322978caf050e25490f87b036c1808a3443c1b009e83440c4000353308307168ca824dc233904c74633816889ac41219309383180bc000352c25340981cb1c51b25611107a836617d8a5844a1bd0a183680d20003525663269794aea51325390f479e36917b8a4c4541b10a183400c2000351ea432617b4af451125791147c23721810a344501bd0a283640da0003517f931f1738ab84e6238104075834916c09d84141a809f83440e80003511183409840b4252b25e911879c36917e8a444501ab0a5837c0ca000350a6d3219744ada501242906476c34f1738a104361a90a003480da0003503ca31f974cac84e9241106c76034617009c84261a109d83340d000034fd2f31316e0ab84f0245108875e34716e09a440419509583200d400034f6783251768ad84f0242906c76434817009e041819d09883280d200034ef9b33b1840b1c51e25d10c479035f17609f841a1a30a4834c0cc00034e8d033397ccaf4518257910c7bc3691798a4c4461b80a1036c0e600034e24830f170cabe4fa24d10b478235b1760a1843a1ad0ab83980e800034db7333197e8b1452426111347b637d1818a604561b90a903900e600034d4ca323173cac44fb24910b077834c1718a144201ad0a083840e600034ce133261790af650f25710e478c34917009c441e1a40a283480d600034c7743139718ac24e7241108c76e34517009ec4361b50a783bc0e400034c0a932c97a4af250d25211047be3731798a144241af0a283440ce00034ba02319172cace4f9249109c78a35d1818a3c4441b20a483600ca00034b33c33117c8b0c51325611107b43751800a584541b90aa83880e400034ac7333217e4b1851b256911079e3651798a204341b50a703700de00034a5b23261778ade50d25110b079e36c17d8a404621b70a003600c6000349f293139708a8e4e5241906476c34317209d04221b20a783680e000034986d32a97d8b1651d25410e07883591788a444461b80a803780da0003491ba3221780af850a25390e078a35d1778a144381b60a183540de000348afd32e97b8b0652225791247ae3721888a844641be0ab03700d600034844c326179caec50a25210b078835217009bc40619b09b03400cc000347da831d9768ab84f024a90ac78235c17b8a084281af09f03540dc0003476f1325975cad650c25211107ae36d17b8a4443a1b50a703b010600034704831f1730ab24f5249108877635016f89e041219e09903500cc00034699b31d9754abe4ed24710c878835817709fc41c19d09d83440c20003462e5324977caec50124c90f479e35617489f042e1b30a183600da000345c473149728ace4ff24f90ac78635e17d8a444441ac0a3836c0ee0003455913229768aca4f924b109878235216f09bc4141a809f03400c8000344eea3211738ac44ef23c906075e34e16f89e441019f09e03380ca00034483332a978cafe51825290d47aa36f17f0a1044c1c10a183880e40003441843271790ad850724c10b478635617409f44281a90a103580e6000343abb32f97b4af450625210f07923561788a2444c1c70a3837c0de0003433ef32997a8b0c524258911c7ae35f1800a4843c1ae0a183740e2000342d5f317970cac44ec246905c7623491738a004381a809703180ca0003426b332697a4b0650625010c078235517809f04221aa0a383580da000341ffe32897b4afe52525991207ae36917e8a604761c10ab839c0e80003419643171734ac64f724610b477434516e09a43fe19809f03580d80003412863399820b3652125811047b43641778a2042a1aa0a683700de000340bb732f17e4b0051325610e47b436117f0a9045a1bd0ac83680e40003404e632b17a8afc50324a90b477e3531720a144341af09d03580d200033fe2432897a0b1452425b90dc77235016f09d041619d099033c0cc00033f75933017bcaf650625190fc7943661788a1c44e1bf0a883980ee00033f0be31b9760acc505248907c76834a17289f84201ab0a103480cc00033ea023281768ae050524b90c478c3581778a3c4421b00a183600ce00033e332337180cb3051d25f113c7dc37f1860aac4721ce0ac03a80f800033dc8331b9750aee50c25310d07a83721858a6444a1c20a603a00ec00033d5b732e17bcb0e52225590cc7903581760a0c4301ae0a103600d400033cf1531d1750ad650224910a47943571750a2c4241a909c03540d2000)) else (if i < 32 then (if i < 31 then 0x3722ec3229758aec50625210f079c36a17d0a4844c1bc0a8836c0dc000371c403211774af250224d10cc79c36117a89f84101a70a103500d40003715b331016fcaa64ec23e102c74e33916f09a84141a70a003500da000370ed133197dcb30522258911c7be36e17c8a044421b30a0833c0d60003707f633997f0b1051225510ec7983671810a3443a1b10a403780e6000370153320177cae650824f10cc78e35f1790a0c4241ac0a383a40f400036fa7e3391830b3452e25c11247be3711860a4c4321a809f034c0d600036f3cd321976cad24f6245908077835c17c0a14438198095830c0ce00036ed2731e1744ad250b25390cc79636017b0a1843e1b50a183600da00036e67a3231764ad24fc249909c7863591770a0c43a1b90a283780e000036df9533c981cb4053b263917c7e63871880a604421ae0a403680e600036d8e131e9730ab64f8243107477c35a1758a2c42a1a809b83440ce00036d22b3221758adc50524810a479635d17a8a3042e1a60a6839c0ee00036cb85324177cae84fc245908878e35917409ec41c1a209b03380d000036c4f53129704ab24ee24110907623531728a004201a609f834c0bc00036be2133697d8b0c50725210f879835d1798a304461b60a1835c0d400036b7a330a968ca724d723a905075034c17009e042e1ae0a1035c0ce00036b0c933097d4b0051625711187b83741880aac4641bc0a503580d000036aa123241784af24fc24910a877035817c0a504561c10aa03840de00036a36b31c9710ab64e623d103075034016e89d44181a009b83440d6000369c8d33917dcb0651b25791187c036d1810a6043e1b40a3033c0ca0003695d63219770ad24fe24810887663531780a144341ac09f83600e0000368f4e3109700aba4f1243909877035717289f04161a809e833c0d800036885a33d9848b4253326191647e237c18a8a944661c50a9839c0fa0003681c931316f4a864e423d905c76034516e099c40419309903180cc000367b0232a97bcb0451b25a10ec7a635f17b0a0c4381b30a003540c400036743b3281774ae651224f10f87b636217e8a544461c10a7838c0de000366dad3149704ac04fc24890a878e35a1778a1441e1a60a0835c0d80003666f43229788b0451d25290f47b637217e0a484541bb0a783780f600036605b31a1708abe4fc247108c76434616f89c840e1a009a83440d800036598e32a97dcb1a52725a912c7be3701878a6445e1c10ad03c80f40003652ee31516f0aa64f3243905874434016a09a440c19509a83580de000364c36328177caec50824c90b878c35817b8a3c45c1c00a883880dc0003645a43189744ac04f7247909c77234b1770a004321ae09e83380cc000363ef831c974cad2504249907c7703581748a0c41a1a309f83300b80003638433249778af050625410dc7aa3731830a3c4521b40a903980d200036317133017c8af8515253111079835c17a8a404541b40a3837c0ee000362ac03231788ae24fe25090ec78835e1798a144341b30a283700ce0003623ea33097d4b0851d25a91307a436417609fc4261b20a383840e6000361d463179710ab04f3240907c7743591748a344521bb0a783ac0e60003616a331f1750ad84f924610b878435217109c440e19c09a03380ca000360fef326978caea50524e90b877a35317109e041e1a509e836c0ca0003609513139700aba4f4247906476034716b09e44341b40a183700ea00036027733b9828b3052725b11387ba37517f0a204321b00a203700d400035fbc131e9758ae44ff24a909477635f1750a184201a70a0837c0e000035f5243211760ada50324b10d079836217989fc41c1a509e03640e400035ee5033297e4b1251d25591187a436e1820a4c4501c00a683640da00035e79532d17bcb0251925a90fc79435f1800a584461b309e03600de00035e0f431d1740abc4f1241109878035c1788a1044a1ab09d83440ca00035da193331818b3a53426091487d637e1868acc48c1d60b0039c0ee00035d3873151708a9c4df23a902c75c34b17209e84241a809f03540ec00035ccf031a9728aba4fb24910b07843561710a2442c1ac0a103400d400035c63b3291798b0a51e25a91087ac3641788a0042019e09b83540d400035bf9131d1744aba4e924590807703521790a244381b009b03380ca00035b8c532e97a4ae250624e10d879035817189bc40219a09883140c200035b23131516e8ab24f5243908476234616e89e441619609583140d200035ab8f31d9728ad050024910a076c34616909c43fe1a009e834c0ce00035a4dc32417b4b0c51225390f47a836217b8a144461b809a83400c8000359e28320173cab44f324910b076c34b16e89c842c19e09583240ca0003597993109710ac04f5246108475c34416589603e819409483240c60003590c533297ecb14514257910c7b236b1818a7844a1b30a4837c0da000358a4730d96a4a8a4d723a902074034216f09dc3fa19809d03600de00035836033a982cb2e52025791187ba36517e0a3444c1af0a383680d4000357cc23191710ab84f3247908077035416f89e841e19a09903480e6000 else 0x38ce5133117c0b1c52225490d078635c1780a0841619e09d03580d000038c7a83211744ad44fd248107877836317d8a1441c1a609c83540dc00038c10831f1730acc4f8243905876a35d17409f44221ac0a2836c0d200038ba5d3269784ad84f4243906c75c3491730a344401b30a6034c0de00038b38c33397d4b1c51f25b11187a836917d0a6c4541bc0a303480d200038acdf31b9720ad24fa24c10b477a34316b89e84281a609e83400da00038a6223289768ad850324a10c878c35417d0a204281a509a833c0cc000389f7131e1734ab64f1243106877634f16f09e44141a509983380ba0003898bb31f9724ac450324990507683451720a0042a1a909e835c0d000038921c3191728aaa4f024810c078834d1778a144261b40a683a40d4000388b623291798aec50c25090a478835116d89f84281ad0a1034c0c40003884e430916a0a844de23910487543431740a1441c1b009d834c0c6000387e4b3171720ad650224810ac79036517b0a204401ac09e03380d80003877933259774ad850424f90d479035017109ec41c1af0a0035c0be0003870e63271798af851024e90bc79635917b0a5444e1bf0a9836c0e2000386a433249754ae250c24c90bc78e3541758a084281ac0a383300c800038638532917c4b0851325490e07843571768a244341a409a83480c0000385d0531016b8a984e423c108475032d16489983fc19b09a83680e200038563633297e0b18512256910c7c037b1810a4c44a1b60a103380c8000384f573369804b3652d25d91447ca3771870a8045c1c20a8837c0dc00038489f3231798b0451925110fc78836617e0a0c4421ac0a283700d200038420d31696d8aa04eb244904875a34417389e84141ad09e83540cc000383b6c3181740ae44f3245908075633d16e89a03fe19709183080c20003834be31b175cae0507251910479035216f09e441a1a40a083580d4000382e3731016c0a9e4e523c905475c33316809ac4061a109b03340dc00038276933917e8b1e52225a911c7ac3601788a0442c1ad09f833c0d400038209433217ecb2c51825511187a236817d8a384461b80a703a80e20003819d93291788aec50625290e479c36517b0a1442819c09a831c0bc00038132831e1720aac4f924a90d478a35917c0a284561cb0aa03880f2000380c7a3231748ae450024a90c879e3651788a3844a1b009e83580d20003805c731e9750ac44f4247108076834e17b0a5c44e1b10a283580dc00037ff17323977cad450725010dc79036117e0a304401b00a083500d000037f853328179cada50824e90b477e34816e8a0c43e1b60a483600e200037f1ba31d175cad650324d90d879235c1770a404441b009d83440d800037eafe3299794af051925310c078835f17b8a2042219909b03200ce00037e43932e17c4b0451325910f47a436917b8a344441ae0a303580c600037dd9931b170cab24f7243104874c34416e09f44241a909a83740d200037d6f531b9754ace50124b10ac79235f17b8a2c4501ba0a603680d400037d03033117a8b04515256110c7b036f17b8a1c43c1a009c83400d800037c99431a1738ac44ff24b909478435617189e441a1a809b03500d400037c2cf33217e0b3052325f11407d43731808a544501bd0a7837c0ee00037bc3a3159718ac44ea243107877234e17489c041c1a409e03500da00037b59831a9744ac44fc246109477234f16b09943f419709803380d200037aee431d96fcabe507249108c76c3531750a344321b009d03500c800037a8503141744ac24f4245908476e35017209ec4261a609803300ce00037a1b131b9748ad44f0240903073033016089743ec19509603300ca000379aef32a97b4b0450b25091207ac36a1830a384441aa0a183440da00037942433417f8b0e51b25a111c7b03651820a384581ba0a883540c8000378d8831316dcab24f7245905c75e33f16809a03f018f09982f80c20003786dc31a1724aca50024e108876e34617489fc42e1a90a203640d8000378024322974cacc4f7248109077e35116e09bc42419f0a3036c0ba00037798931316f4a9e4ed23d102473834117009c441819b09a83440d40003772fe30e96e4aa04e32379008738334167899c40e1aa09c03480d6000376c5331c1760ad450f25310b078a35717209ec41a1a40a103400d800037659e3201764ad24fc24a109c79635917c0a044281ad09c835c0e0000375ee83271798aec50724e90b477e3551728a0c4281a6098833c0d000037584531d1758aca4f323f906476034b16e89bc42219b09783100ba0003751af3191720aae4fd24e10e07a236117c8a204321b50a4836c0dc000374b02329979cafe51224e10f87a836417f0a0042a1a809f832c0c60003744743111710adc50224890b47843521758a2441c1b20a2037c0ca000373dc63289790ad64fe24b90a478c35d1798a2043e1b40a303600d200037371d32417a4afa51625790fc79636417f0a004201a409d03480ce00037305632b97c4b2051625a90fc79235e1780a2042e1a60a103580d600037299632c17acb0451925610f47aa3681808a404441a709f83540c8000) else (if i < 33 then 0x3a799230b96e0a824d7239906074c335167899c3e418d08f82f40b00003a72dc32b17ccb0c51a25390e879e35e1778a244341b60a2037c0d60003a6c3b31b1748acc4f2243109876635417109e84361b40a603900d80003a65a630e16c8a864d623a903474a33e16789803f619d09e03480dc0003a5f2230c16a8a864cc2318fdc72832a16089543e21a0099835c0d40003a5867327977cae84fc24c10b878c3531760a284461b50a383740ec0003a51be3239784af051025210b477e35717a8a1443c1b30a003440bc0003a4b0e322977cad8500245907877835617509e04241a409d83380ba0003a447331c972cab44f123b902875834316f8a044321ac0a6837c0da0003a3de831516e8aa84f2244107c75434e17109e84181a409e03480d20003a375e314172cabe4f4245109478c35b1738a044301ae09c83500da0003a30ba31f9740ae250724e90c878a35e1780a1c4381a70a383680e00003a2a04326174cad04f524a10d879435e17909ec42a1ac09d035c0d20003a236931a9724ac850324b90cc78c3671750a1043c1b60a603840e40003a1cd63119700abe4f02459078776356172099440819f09d83280c80003a161532b97a8aec51325210e879e35f17a89f04181a009d83440ce0003a0f5732a9788ade50424d10f479035717609f442e1a609d83500d40003a08ab32497a0aec50c25010e879a36417a0a344381af0a5036c0c60003a021531616f8aaa4ea242907876834f17389d443a1af0a503740e000039fb3233e1848b5c544265114c7c836817e0a5045e1ba0a5836c0d800039f4903239754ade507246906075c3441700a0441e1a609d831c0bc00039edf931e1744ace50224890b479035c17a8a284381af0a383680d800039e73532b97a8b0c51325310b878035817c8a304221a509803180d000039e0af30e16ecaae4f824b90a47883561750a184321af0a383980e200039d9f3325978caf04fe24e10bc79235517309f441a1a50a003640e600039d33b32e17f0b2651825090c87963581760a0c43c1b00a303580d600039cc883249770ae24ff244107476034d17289d041a19e09a032c0c600039c5d63231764ace4f824710b477c34a17509f843c1a209c832c0d400039bf2f31e175cad24f7246109877a3611798a3c4481ad0a483580d400039b89531f173caca50024810bc79c35d1778a204441b30a303700d600039b1ee31d1748abc4f224490ac7763561758a0843a1b40a1035c0c400039ab2f33197c4b0651624c90cc79835f17a8a304321b809c83480dc00039a46133297fcb2653326311687d237b1828a6044c1c10a783780da000399dc231a1734ab44f3249908c7703551790a1c4321a80a3038c0e400039970d3201734ab24eb24910a077e3581780a244401af0a5036c0d400039903333917dcb2251125790fc7ae3631780a1842819809903440da00039897732a1798ae650625090cc78635917a0a044261ae0a283600d80003982a9327978cb06516253910c7ae36517d8a144421bd0a183940d0000397c2a30d96f4aa84f2241106475234816a89ec42a1aa0a803780e00003975743241774ae44f724b908075c34917109ec41a1a909e03300ca000396ec03229780ae850124c10cc78635e1748a0c4201ac09a034c0d200039682031d975cae050724e10c879835f17589e842c1b409e83200be00039616e326979caf451025010fc7c23671800a344341aa0a0035c0de000395aa832e97c0b10526256910c7b83671800a5c44c1c50ab03a80e200039541931196b8a684d32360ffc73832e16889a840c1a20a083680e4000394d5c3289798b0250f25210f879e36a17f0a5844e1bf0ab03a40de00039469d32c97ccb1252125811107c036e1838a8446c1c60ac03a80e4000393fe73271798b0650524c10bc7823561750a0c42c1ba0a583500ce00039392d32b17b8afe51a25b10f87a436117d0a304441b209f83400dc000393264329979cafa51625210e87a43681790a204361a80a0835c0d8000392be630a16aca904e723b104c75e33a16509883ec19009903440e200039252b32b97c8b1c52325610f87a636317e0a6c4621d00ae83b00ec000391e83322177cadc4fe25411047aa36c1798a304421b40a603780e80003917d132817a0aea50a24d90b478235a1770a284481b10a503780da00039111032e17ccb1a51425810ec7a436817b8a384441ba0a1035c0d8000390a5732b97a8afc50b25190f87a636e1790a104301a909d034c0d40003903bd31396ecaae4f324310587603411720a044241a709b83500d200038fd2131516f4ab84f2244107475833f16a89c841c1a809f83280c400038f66232c17a8b1651f25810f479e3631800a644581c60ac03a80e800038efb731b1710aa84e9239101472a33116509c04181a309b83340c400038e90b3251780b0251225390e879e35917b8a4843e1b80ac03580de00038e273317970caa84ed24910a47743531770a1443c1a909f03400ce00038dbc4322977cad850424a90cc79e35a17c8a184461bb0a683680ea00038d51f3189718aae4f724810ac77034d17609e441c1ae0a0837c0e2000 else (if i < 34 then 0x3c24b831596ecaa84e823b905875434716d09d04321ab09e03480d80003c1e203171710ab64e9247109078035017309fc4321a70a083580d60003c177a31e9754ac6500246109077434c17309c040e19c09b83300b60003c10d531c974cacc4f924b909878034f16d89f442a1aa09f83280ce0003c0a4930f96ecaae4f5249109476c34d16f89d840c1a209e83480d00003c038232d97e4b0450f24f90cc7843531738a0443e1b40a583840c80003bfccb325977cae450624710947883591780a1043e1b30a203700e00003bf61b321979cafc51425211047aa36a17e8a584501ba0a5837c0e20003bef5e3271770ad44f424990c078234d17509dc4301a80a003600e60003be8c83199700ab04f6244107076834d17189c842e1b00a083780e00003be22931b9758ad850124c108878235317089ec4261a609f03540dc0003bdb6b3279788ae84f924590a475834516d89dc41e1a90a003540d40003bd4cc3179734ac24f8246105875833817209f042a1aa09883300c00003bce2a3199754ace4fe245907c77a35217009c84081a309e835c0d20003bc78331b9790ae24ff24990ac79a36517c8a3c4481b90a983800fc0003bc0ba327178cafc51025110bc78a3531730a004441ae0a183600cc0003bba18317173cacc4fc24990b478835917a09f84321a409e03600d00003bb3273419848b5654026a11cc7f23871890a7c4541bd09f035c0da0003bac8b3189708ab04f6249908476e34416c09c040619d09b031c0bc0003ba5e63211780af250d25490f079c36b1850a644441b20a203880d00003b9f353221750adc4f924890b079235a17509e042a1a109d03500c20003b98663351804b2852425a11007a236c17f0a4844a1b40ad03bc0fa0003b91be31a9748aaa4e623e104073032c166097c3f619609883300c20003b8b2731716ecaae4f3249107875e34e17089ec41819d09b83100bc0003b84773239768acc4f424e10c078e3621778a0041c19e097833c0d20003b7dbb325977cae8508255911c7ba3741800a4043c1ba0a883640d40003b7709321173cace50524e909477e34816889e440a19e09b03280b20003b704a3269784b2051d25590f47a636017709f44261ae0a683840e40003b69883279784af850a24f90a47743581748a0042819809e03400c40003b62d631e972caac4ee248109877834c17489f84361b40a6838c0f20003b5c1232d17acb0e51f25310f87aa36d17c8a344421b009e83580ce0003b557c3189760ac04e623f905c77836317a0a6044e1bc0a783640d20003b4ed23231780aea50b24d10c477635317409c441c1a009c031c0bc0003b480832e17a0af4517254911c7b436d1820a384401ac0a203780e40003b416931b970cab64f3245107476a34a17509d840e1a109e03180d40003b3ac931f9728abc4f4245106477434f1778a044401b40a303580de0003b343a31416d4aa44de239103074633616909783f219009482f40cc0003b2d7432c17a0b0251325390d07723561708a0c4361af0a403600dc0003b26df31516dca924db231900473833816409b44061a009f03440e00003b2039318971cad050525110d879e35116f8a0440a19d09a834c0d60003b19a831596ecaae4f623f1038750332164098840019a09d036c0c20003b130631d9730aaa4f824910ac77235316b89e842e1ab09c83200be0003b0c6a31e9708aa84ed244907075c34717289d44081a109c034c0da0003b05d43181724aa04e6242105875a34e16f0a004441b20a683600d00003afeff33617e4b2852b25e913c7d437e1880a844681ca0ad83a40d60003af83732a9784adc50324e90d879235d1780a2042e1b10a003540c40003af13f346989cb6854626611ac7ea39318e8ac046a1cc0a983780d00003aeaae314170caa04ea245108c78635c17d0a2c42a1b40a383680ce0003ae43630e16d0aba4ef248908c77035e1780a284441b509e03440c60003add7a3249770ae050824d109478435b1768a2043e1b40a783a00ec0003ad6bf32717c4b0451925391007b036617e8a884521be0a683ac0e20003ad01831a1738ada4fa243904474e33b16709a440819a09503340be0003ac95e32b17acb1851d25a912c7be36e17d8a704521ba09f83240c40003ac2d231296dca9c4ea245908076e34917309c84061a209b832c0b80003abc2e3199704aba4e8244908077c35417c0a144321b10a4036c0de0003ab5943151710aa04dd23c105076234916b09d441a1ba0a503780dc0003aaf0a30c16c0a904e323c101c74a34716d89f04081a0099831c0cc0003aa8643201748ac24ea243105c76e3501738a084221ab09e03780cc0003aa1b231f9754ad24f8245909078c35b1800a8c4661c10ab83a40f20003a9ae533397ccb1051525090e87a83671778a304301a709d03600dc0003a944431b973cac04f223f908077034617409d441a1a609e03500d20003a8d943199700aa24e9242909877e34816c09a84141a909f834c0d60003a86f53169708ab44f323d103875033a16a09a840619509d83280b60003a801733a9814b2652a26211647c636e1830a4444a1c10a803880e6000 else 0x3cbe1f0000000ad250b24f10f077c34917309bc4181a60a5038c0dc0003cb77831d1740ac84fb24c90d47963531718a004361af0a0034c0d20003cb0d0321176cad04fb24b90b878635416e89f44481aa09c034c0e40003caa1232417a8afa502249908877235017209e441c1ad09983440be0003ca3503269778ae250625310d47aa3731828a4c4561bf0a303740da0003c9ca631d9770ad850024890a077835617389d041e1a309d03440d20003c9612317971cac24ee246907c75634016989683de19709b834c0c60003c8f5732c97e4b0250f25190d87a036717e0a344561c00a983ac0dc0003c887f32f97e8b0e52125491107c03731890ab047a1ce0ae83980e40003c81d03219770ae650724f90e079a36417e8a504661c30a883700ce0003c7b3c31116f4a9c4f223f106075034616a09a03fa19809803040c40003c748232c17c4afa50c24c90b077834016d89e84161a909b833c0d60003c6dbb32c1790af650a25410cc77a3541728a1c4241ad0a183540ce0003c672b30b96c8a9e4ef243907077e3561780a104341b209e83500c40003c608431e177cb0c51e25a11187ba36a1800a444401af0a003600d80003c59e131c174cad450024a90b877a35317489f442e1b00a683740ea0003c533b31c175caea51725490ec78e3501770a0441c1a109a83280c60003c4ca33199734acc504243908477835617589e84201aa09e83440c40003c45e632d97ccb0850424a90ac78c36b1760a2c4361ac09f83700d80003c3f57316172cac44f1243907076a35017189f44261a609f83340ca0003c38b131c1740aca4fa248908c76434d17389c440419b09983140be0003c321c31b172cac850825290e479e3641788a084261a30a103440ce0003c2b4133c1810b2c52b25b91247b837517e8a544601cc0a983740d8000))))))

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



private theorem b18070 : covered 18070 18139 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18139 : covered 18139 18207 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18207 : covered 18207 18276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18276 : covered 18276 18345 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18345 : covered 18345 18414 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18414 : covered 18414 18482 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18482 : covered 18482 18551 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18551 : covered 18551 18620 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18620 : covered 18620 18689 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18689 : covered 18689 18757 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18757 : covered 18757 18826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18826 : covered 18826 18894 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18894 : covered 18894 18963 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18963 : covered 18963 19031 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19031 : covered 19031 19100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19100 : covered 19100 19169 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19169 : covered 19169 19238 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19238 : covered 19238 19306 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19306 : covered 19306 19375 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19375 : covered 19375 19444 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19444 : covered 19444 19513 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19513 : covered 19513 19581 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19581 : covered 19581 19650 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19650 : covered 19650 19719 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19719 : covered 19719 19788 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19788 : covered 19788 19856 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19856 : covered 19856 19925 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19925 : covered 19925 19993 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b19993 : covered 19993 20062 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20062 : covered 20062 20130 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20130 : covered 20130 20199 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20199 : covered 20199 20268 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20268 : covered 20268 20337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20337 : covered 20337 20405 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20405 : covered 20405 20474 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20474 : covered 20474 20543 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20543 : covered 20543 20612 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20612 : covered 20612 20680 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20680 : covered 20680 20749 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20749 : covered 20749 20818 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20818 : covered 20818 20887 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20887 : covered 20887 20955 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b20955 : covered 20955 21024 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21024 : covered 21024 21093 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21093 : covered 21093 21162 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21162 : covered 21162 21230 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21230 : covered 21230 21299 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21299 : covered 21299 21368 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21368 : covered 21368 21437 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21437 : covered 21437 21505 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21505 : covered 21505 21574 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21574 : covered 21574 21643 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21643 : covered 21643 21712 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21712 : covered 21712 21780 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21780 : covered 21780 21849 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21849 : covered 21849 21918 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21918 : covered 21918 21987 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b21987 : covered 21987 22055 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22055 : covered 22055 22124 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22124 : covered 22124 22192 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22192 : covered 22192 22261 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22261 : covered 22261 22329 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22329 : covered 22329 22398 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22398 : covered 22398 22467 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22467 : covered 22467 22536 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22536 : covered 22536 22604 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22604 : covered 22604 22673 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22673 : covered 22673 22742 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22742 : covered 22742 22811 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22811 : covered 22811 22879 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22879 : covered 22879 22948 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b22948 : covered 22948 23017 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23017 : covered 23017 23086 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23086 : covered 23086 23154 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23154 : covered 23154 23223 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23223 : covered 23223 23292 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23292 : covered 23292 23361 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23361 : covered 23361 23429 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23429 : covered 23429 23498 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23498 : covered 23498 23567 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23567 : covered 23567 23636 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23636 : covered 23636 23704 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23704 : covered 23704 23773 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23773 : covered 23773 23842 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23842 : covered 23842 23911 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23911 : covered 23911 23979 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b23979 : covered 23979 24048 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24048 : covered 24048 24117 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24117 : covered 24117 24186 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24186 : covered 24186 24254 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24254 : covered 24254 24323 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24323 : covered 24323 24391 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24391 : covered 24391 24460 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24460 : covered 24460 24528 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24528 : covered 24528 24597 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24597 : covered 24597 24666 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24666 : covered 24666 24735 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24735 : covered 24735 24803 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24803 : covered 24803 24872 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24872 : covered 24872 24941 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b24941 : covered 24941 25010 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25010 : covered 25010 25078 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25078 : covered 25078 25147 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25147 : covered 25147 25216 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25216 : covered 25216 25285 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25285 : covered 25285 25353 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25353 : covered 25353 25422 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25422 : covered 25422 25491 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25491 : covered 25491 25560 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25560 : covered 25560 25628 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25628 : covered 25628 25697 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25697 : covered 25697 25766 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25766 : covered 25766 25835 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25835 : covered 25835 25903 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25903 : covered 25903 25972 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b25972 : covered 25972 26041 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26041 : covered 26041 26110 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26110 : covered 26110 26178 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26178 : covered 26178 26247 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26247 : covered 26247 26316 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26316 : covered 26316 26385 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26385 : covered 26385 26453 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26453 : covered 26453 26522 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26522 : covered 26522 26590 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26590 : covered 26590 26659 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26659 : covered 26659 26727 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26727 : covered 26727 26796 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26796 : covered 26796 26865 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26865 : covered 26865 26934 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b26934 : covered 26934 27002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27002 : covered 27002 27071 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27071 : covered 27071 27140 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27140 : covered 27140 27209 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27209 : covered 27209 27277 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27277 : covered 27277 27346 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27346 : covered 27346 27415 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27415 : covered 27415 27484 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27484 : covered 27484 27552 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27552 : covered 27552 27621 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27621 : covered 27621 27690 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27690 : covered 27690 27759 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27759 : covered 27759 27827 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27827 : covered 27827 27896 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27896 : covered 27896 27965 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b27965 : covered 27965 28034 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28034 : covered 28034 28102 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28102 : covered 28102 28171 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28171 : covered 28171 28240 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28240 : covered 28240 28309 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28309 : covered 28309 28377 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28377 : covered 28377 28446 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28446 : covered 28446 28515 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28515 : covered 28515 28584 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28584 : covered 28584 28652 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28652 : covered 28652 28721 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28721 : covered 28721 28789 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28789 : covered 28789 28858 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28858 : covered 28858 28926 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28926 : covered 28926 28995 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b28995 : covered 28995 29064 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29064 : covered 29064 29133 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29133 : covered 29133 29201 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29201 : covered 29201 29270 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29270 : covered 29270 29339 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29339 : covered 29339 29408 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29408 : covered 29408 29476 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29476 : covered 29476 29545 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29545 : covered 29545 29614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29614 : covered 29614 29683 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29683 : covered 29683 29751 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29751 : covered 29751 29820 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29820 : covered 29820 29889 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29889 : covered 29889 29958 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b29958 : covered 29958 30026 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30026 : covered 30026 30095 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30095 : covered 30095 30164 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30164 : covered 30164 30233 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30233 : covered 30233 30301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30301 : covered 30301 30370 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30370 : covered 30370 30439 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30439 : covered 30439 30508 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30508 : covered 30508 30576 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30576 : covered 30576 30645 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30645 : covered 30645 30714 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30714 : covered 30714 30783 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30783 : covered 30783 30851 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30851 : covered 30851 30920 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30920 : covered 30920 30988 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b30988 : covered 30988 31057 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31057 : covered 31057 31125 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31125 : covered 31125 31194 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31194 : covered 31194 31263 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31263 : covered 31263 31332 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31332 : covered 31332 31400 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31400 : covered 31400 31469 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31469 : covered 31469 31538 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31538 : covered 31538 31607 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31607 : covered 31607 31675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31675 : covered 31675 31744 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31744 : covered 31744 31813 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31813 : covered 31813 31882 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31882 : covered 31882 31950 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b31950 : covered 31950 32019 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32019 : covered 32019 32088 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32088 : covered 32088 32157 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32157 : covered 32157 32225 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32225 : covered 32225 32294 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32294 : covered 32294 32363 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32363 : covered 32363 32432 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32432 : covered 32432 32500 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32500 : covered 32500 32569 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32569 : covered 32569 32638 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32638 : covered 32638 32707 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32707 : covered 32707 32775 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32775 : covered 32775 32844 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32844 : covered 32844 32913 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32913 : covered 32913 32982 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b32982 : covered 32982 33050 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33050 : covered 33050 33119 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33119 : covered 33119 33187 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33187 : covered 33187 33256 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33256 : covered 33256 33324 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33324 : covered 33324 33393 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33393 : covered 33393 33462 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33462 : covered 33462 33531 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33531 : covered 33531 33599 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33599 : covered 33599 33668 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33668 : covered 33668 33737 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33737 : covered 33737 33806 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33806 : covered 33806 33874 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33874 : covered 33874 33943 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b33943 : covered 33943 34012 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34012 : covered 34012 34081 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34081 : covered 34081 34149 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34149 : covered 34149 34218 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34218 : covered 34218 34287 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34287 : covered 34287 34356 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34356 : covered 34356 34424 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34424 : covered 34424 34493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34493 : covered 34493 34562 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34562 : covered 34562 34631 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34631 : covered 34631 34699 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34699 : covered 34699 34768 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34768 : covered 34768 34837 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34837 : covered 34837 34906 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34906 : covered 34906 34974 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b34974 : covered 34974 35043 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b35043 : covered 35043 35112 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b35112 : covered 35112 35181 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 18070 35181 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b18070 (joinCoverage b18139 b18207)) (joinCoverage (joinCoverage b18276 b18345) (joinCoverage b18414 b18482))) (joinCoverage (joinCoverage (joinCoverage b18551 b18620) (joinCoverage b18689 b18757)) (joinCoverage (joinCoverage b18826 b18894) (joinCoverage b18963 b19031)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b19100 b19169) (joinCoverage b19238 b19306)) (joinCoverage (joinCoverage b19375 b19444) (joinCoverage b19513 b19581))) (joinCoverage (joinCoverage (joinCoverage b19650 b19719) (joinCoverage b19788 b19856)) (joinCoverage (joinCoverage b19925 b19993) (joinCoverage b20062 b20130))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b20199 (joinCoverage b20268 b20337)) (joinCoverage (joinCoverage b20405 b20474) (joinCoverage b20543 b20612))) (joinCoverage (joinCoverage (joinCoverage b20680 b20749) (joinCoverage b20818 b20887)) (joinCoverage (joinCoverage b20955 b21024) (joinCoverage b21093 b21162)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b21230 b21299) (joinCoverage b21368 b21437)) (joinCoverage (joinCoverage b21505 b21574) (joinCoverage b21643 b21712))) (joinCoverage (joinCoverage (joinCoverage b21780 b21849) (joinCoverage b21918 b21987)) (joinCoverage (joinCoverage b22055 b22124) (joinCoverage b22192 b22261)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b22329 (joinCoverage b22398 b22467)) (joinCoverage (joinCoverage b22536 b22604) (joinCoverage b22673 b22742))) (joinCoverage (joinCoverage (joinCoverage b22811 b22879) (joinCoverage b22948 b23017)) (joinCoverage (joinCoverage b23086 b23154) (joinCoverage b23223 b23292)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b23361 b23429) (joinCoverage b23498 b23567)) (joinCoverage (joinCoverage b23636 b23704) (joinCoverage b23773 b23842))) (joinCoverage (joinCoverage (joinCoverage b23911 b23979) (joinCoverage b24048 b24117)) (joinCoverage (joinCoverage b24186 b24254) (joinCoverage b24323 b24391))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b24460 (joinCoverage b24528 b24597)) (joinCoverage (joinCoverage b24666 b24735) (joinCoverage b24803 b24872))) (joinCoverage (joinCoverage (joinCoverage b24941 b25010) (joinCoverage b25078 b25147)) (joinCoverage (joinCoverage b25216 b25285) (joinCoverage b25353 b25422)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b25491 b25560) (joinCoverage b25628 b25697)) (joinCoverage (joinCoverage b25766 b25835) (joinCoverage b25903 b25972))) (joinCoverage (joinCoverage (joinCoverage b26041 b26110) (joinCoverage b26178 b26247)) (joinCoverage (joinCoverage b26316 b26385) (joinCoverage b26453 b26522))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b26590 (joinCoverage b26659 b26727)) (joinCoverage (joinCoverage b26796 b26865) (joinCoverage b26934 b27002))) (joinCoverage (joinCoverage (joinCoverage b27071 b27140) (joinCoverage b27209 b27277)) (joinCoverage (joinCoverage b27346 b27415) (joinCoverage b27484 b27552)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b27621 b27690) (joinCoverage b27759 b27827)) (joinCoverage (joinCoverage b27896 b27965) (joinCoverage b28034 b28102))) (joinCoverage (joinCoverage (joinCoverage b28171 b28240) (joinCoverage b28309 b28377)) (joinCoverage (joinCoverage b28446 b28515) (joinCoverage b28584 b28652))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b28721 (joinCoverage b28789 b28858)) (joinCoverage (joinCoverage b28926 b28995) (joinCoverage b29064 b29133))) (joinCoverage (joinCoverage (joinCoverage b29201 b29270) (joinCoverage b29339 b29408)) (joinCoverage (joinCoverage b29476 b29545) (joinCoverage b29614 b29683)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b29751 b29820) (joinCoverage b29889 b29958)) (joinCoverage (joinCoverage b30026 b30095) (joinCoverage b30164 b30233))) (joinCoverage (joinCoverage (joinCoverage b30301 b30370) (joinCoverage b30439 b30508)) (joinCoverage (joinCoverage b30576 b30645) (joinCoverage b30714 b30783)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b30851 (joinCoverage b30920 b30988)) (joinCoverage (joinCoverage b31057 b31125) (joinCoverage b31194 b31263))) (joinCoverage (joinCoverage (joinCoverage b31332 b31400) (joinCoverage b31469 b31538)) (joinCoverage (joinCoverage b31607 b31675) (joinCoverage b31744 b31813)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b31882 b31950) (joinCoverage b32019 b32088)) (joinCoverage (joinCoverage b32157 b32225) (joinCoverage b32294 b32363))) (joinCoverage (joinCoverage (joinCoverage b32432 b32500) (joinCoverage b32569 b32638)) (joinCoverage (joinCoverage b32707 b32775) (joinCoverage b32844 b32913))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b32982 b33050) (joinCoverage b33119 b33187)) (joinCoverage (joinCoverage b33256 b33324) (joinCoverage b33393 b33462))) (joinCoverage (joinCoverage (joinCoverage b33531 b33599) (joinCoverage b33668 b33737)) (joinCoverage (joinCoverage b33806 b33874) (joinCoverage b33943 b34012)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b34081 b34149) (joinCoverage b34218 b34287)) (joinCoverage (joinCoverage b34356 b34424) (joinCoverage b34493 b34562))) (joinCoverage (joinCoverage (joinCoverage b34631 b34699) (joinCoverage b34768 b34837)) (joinCoverage (joinCoverage b34906 b34974) (joinCoverage b35043 b35112))))))))

private theorem index_mono : Monotone index := monotone_nat_of_le_succ fun n => by
  rcases wheel_step n with ⟨eq,_⟩ | ⟨eq,_⟩ <;> omega

private theorem starting_block : 18070 ≤ index 34751024/512 := by decide +kernel
private theorem starting_value : fast 34751024=2132375 := by decide +kernel

theorem fast_correct (anchor : Nat.primeCounting 34751024=2132375) (n : ℕ) (low : 34751024≤n) (bound : n≤67545646) :
    fast n=Nat.primeCounting n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases first : n+1=34751024
    · rw [first,anchor]
      exact starting_value
    · have past : 34751024≤n := by omega

      have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih past (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤67545646 by omega)
        have within : index n / 512 < 35181 := by omega
        have lower : index 34751024/512 ≤ index n/512 := Nat.div_le_div_right (index_mono past)
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

theorem prime_ok (n : ℕ) (hn : n≤67545646) : prime n=true ↔ n.Prime := quick_ok hn

end RangePrimeA26


open Finset
namespace CorrectionSmall26

private def contribution (x y : ℕ) (big little : ℕ → ℕ) (prime : ℕ → Bool) (p : ℕ) : ℕ :=
  if y < p then if prime p then big (x/p) - little (p-1) else 0 else 0

private def blockSum (f : ℕ → ℕ) (lo len val : ℕ) : Prop :=
  ((List.range' lo len).map f).sum = val

private theorem join_sums (f : ℕ → ℕ) {lo a b u v : ℕ}
    (h : blockSum f lo a u) (k : blockSum f (lo+a) b v) :
    blockSum f lo (a+b) (u+v) := by
  unfold blockSum at *
  rw [← List.range'_append_1,List.map_append,List.sum_append,h,k]

private theorem right_from_blocks {x y z l b small value : ℕ} (big little : ℕ → ℕ) (prime : ℕ → Bool)
    (ok : ∀ n, l≤n → n≤b → big n = Nat.primeCounting n)
    (okay : ∀ n, n ≤ small → little n = Nat.primeCounting n)
    (prime_ok : ∀ n, n ≤ small → (prime n=true ↔ n.Prime))
    (hz : z ≤ small) (bottom : l≤x/z) (hq : x/(y+1)≤b)
    (result : blockSum (contribution x y big little prime) 0 (z+1) value) :
    (∑ p ∈ (Nat.primesLE z).filter (y < ·),
      (Nat.primeCounting (x/p) - Nat.primeCounting (p-1))) = value := by
  have same : (Nat.primesLE z).filter (y<·) =
      (Finset.range (z+1)).filter (fun p => y<p ∧ p.Prime) := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,Finset.mem_range,Nat.lt_succ_iff]
    tauto
  rw [same,Finset.sum_filter]
  calc
    _ = ∑ p ∈ Finset.range (z+1), contribution x y big little prime p := by
      apply Finset.sum_congr rfl
      intro p member
      have pb : p ≤ small := by have := Finset.mem_range.mp member; omega
      by_cases large : y<p
      · by_cases hp : p.Prime
        · have ub : x/p ≤ x/(y+1) := Nat.div_le_div_left (show y+1≤p by omega) (by omega)
          have lb : l≤x/p := bottom.trans (Nat.div_le_div_left (Nat.le_of_lt_succ (Finset.mem_range.mp member)) hp.pos)
          simp [contribution,large,hp,(prime_ok p pb).mpr hp,ok _ lb (le_trans ub hq),okay _ (by omega : p-1 ≤ small)]
        · have no : prime p=false := Bool.eq_false_iff.mpr (mt (prime_ok p pb).mp hp)
          simp [contribution,large,hp,no]
      · simp [contribution,large]
    _ = ((List.range (z+1)).map (contribution x y big little prime)).sum := by
      have rng : Finset.range (z+1) = (List.range (z+1)).toFinset := by ext p; simp
      rw [rng]
      exact List.sum_toFinset (contribution x y big little prime) (List.nodup_range (n:=z+1))
    _ = value := by
      rw [List.range_eq_range']
      exact result

private abbrev term := contribution 555157672301 8218 RangePrimeA26.fast FastDenseControl.fast FastDenseControl.prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))

private theorem before : blockSum term 0 8219 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 8218 < p := by omega
  simp [term,contribution,no]

private theorem r8219 : blockSum term 8219 484 213177332 := by unfold blockSum; decide +kernel

private theorem r8703 : blockSum term 8703 485 202316886 := by unfold blockSum; decide +kernel

private theorem r9188 : blockSum term 9188 485 189009622 := by unfold blockSum; decide +kernel

private theorem r9673 : blockSum term 9673 485 177024335 := by unfold blockSum; decide +kernel

private theorem r10158 : blockSum term 10158 484 166042014 := by unfold blockSum; decide +kernel

private theorem r10642 : blockSum term 10642 485 152814253 := by unfold blockSum; decide +kernel

private theorem r11127 : blockSum term 11127 485 140883613 := by unfold blockSum; decide +kernel

private theorem r11612 : blockSum term 11612 485 141048561 := by unfold blockSum; decide +kernel

private theorem r12097 : blockSum term 12097 484 152125090 := by unfold blockSum; decide +kernel

private theorem r12581 : blockSum term 12581 485 141441577 := by unfold blockSum; decide +kernel

private theorem r13066 : blockSum term 13066 485 118945337 := by unfold blockSum; decide +kernel

private theorem r13551 : blockSum term 13551 485 129684740 := by unfold blockSum; decide +kernel

private theorem r14036 : blockSum term 14036 485 104108620 := by unfold blockSum; decide +kernel

private theorem r14521 : blockSum term 14521 485 124024864 := by unfold blockSum; decide +kernel

private theorem r15006 : blockSum term 15006 485 120182268 := by unfold blockSum; decide +kernel

private theorem r15491 : blockSum term 15491 485 114548641 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem after_cut : blockSum term 8219 7757 2387377753 := (join_sums term (lo:=8219) (a:=3878) (b:=3879) (join_sums term (lo:=8219) (a:=1939) (b:=1939) (join_sums term (lo:=8219) (a:=969) (b:=970) (join_sums term (lo:=8219) (a:=484) (b:=485) r8219 r8703) (join_sums term (lo:=9188) (a:=485) (b:=485) r9188 r9673)) (join_sums term (lo:=10158) (a:=969) (b:=970) (join_sums term (lo:=10158) (a:=484) (b:=485) r10158 r10642) (join_sums term (lo:=11127) (a:=485) (b:=485) r11127 r11612))) (join_sums term (lo:=12097) (a:=1939) (b:=1940) (join_sums term (lo:=12097) (a:=969) (b:=970) (join_sums term (lo:=12097) (a:=484) (b:=485) r12097 r12581) (join_sums term (lo:=13066) (a:=485) (b:=485) r13066 r13551)) (join_sums term (lo:=14036) (a:=970) (b:=970) (join_sums term (lo:=14036) (a:=485) (b:=485) r14036 r14521) (join_sums term (lo:=15006) (a:=485) (b:=485) r15006 r15491))))
private theorem rows : blockSum term 0 15976 2387377753 :=
  join_sums term (lo:=0) (a:=8219) (b:=7757) before after_cut

theorem sum_from_quotients (baseCount : Nat.primeCounting 34751024=2132375) :
    (∑ p ∈ (Nat.primesLE 15975).filter (8218 < ·),
      (Nat.primeCounting (555157672301/p) - Nat.primeCounting (p-1))) = 2387377753 :=
  right_from_blocks (l:=34751024) (b:=67545646) (small:=25123)
    RangePrimeA26.fast FastDenseControl.fast FastDenseControl.prime (RangePrimeA26.fast_correct baseCount) FastDenseControl.fast_correct FastDenseControl.prime_ok
    (by decide) (by decide) (by decide) rows

end CorrectionSmall26

namespace CorrectionSmall26
theorem exact_sum : (∑ p ∈ (Nat.primesLE 15975).filter (8218 < ·),
    (Nat.primeCounting (555157672301/p) - Nat.primeCounting (p-1)))=2387377753 :=
  sum_from_quotients RankWheel34751.first_anchor
end CorrectionSmall26
