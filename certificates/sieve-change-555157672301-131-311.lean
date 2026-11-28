import FormalConjectures.OEIS.«247824»

/-!
# Sieve counts at 555,157,672,301 between prime cutoffs 131 and 311

For integers from 1 through 555,157,672,301, this certificate counts the additional
values removed when the prime cutoff rises from 131 to 311.
The Legendre recurrence checks successive groups of 8 primes, uses a wheel of period 30,030 and prime counts
through 100,000. The identities adapt Physbuzz's A247824 reduction and
the Palomar proof of Daniel Veljjanoski and rleshner (Apache-2.0). The recurrence carries the number
of primes already sieved and uses it when a square bound terminates a branch.
-/

namespace Sieve555157672301From131To311

namespace ShortPeriod30030

open Finset

def cop (n : ℕ) : Bool := decide (n%2≠0 ∧ n%3≠0 ∧ n%5≠0 ∧ n%7≠0 ∧ n%11≠0 ∧ n%13≠0)

private def pop (x : ℕ) : ℕ :=
  let a := x - ((x >>> 1) &&& 0x5555555555555555)
  let b := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
  let c := (b+(b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  ((c*0x0101010101010101) >>> 56)%256

private def packet (i : ℕ) : ℕ := (if i < 7 then (if i < 3 then (if i < 1 then 0x17c808228220808a208017108200220a080288201648228200a00a288200159228800a08a080200014c2882020882882820013f0a20a00a2802802801328202082208282282012520808a08808220a201190808228028228a00010c800a28808228800a010108800820228a202000f58020828008a20a0800e7a28008028220a08a00dc208202282008088200d08808020a2020822800c4820220a00a00a28000b628228820a082088200ab0208a20200808828009f208a20008a280280009228a20a00a0080822008702208088288082200079a20808220828208a006d00a00a208282280200620a08208820028a000056208828808008a202004a08a28028020220a0003e88208282280208080031228800220a20a082002608028228800800a2001a8028208820a00a08000d800228a202088288000028208a20a08a0002 else (if i < 2 then 0x30728808200a20a000202fa8828228a00200a2002ec828208820a08a08802e0202202202088288202d40208a00808a2802802c7028a00208a20828202bc202208082288080202af0820a0822880822802a2a00a00a088282280029620808808020228a2028c0200828800208a20027ea08828028028820a027208a208282082208002660a288082202202080258228820228a00a00a024d08828020820208a002418820220a200088280236828208800a082200022928028a20a0820082021d8028220808a280080210220a20a002288082020328200a008288282201f78820a08a0082020801eba20208828028208001df20a08a28020008a001d30a00a2082802822001c5008a28808220a20a01ba08208828220800a001ad022882822882080801a1a08820228a000088019520028208a20a002201898008028a20a08820 else 0x48f8228028228a00a000482a20808228820a080047608820028a202088204680808208a20a08a28045c028028220a088208045020228200808a288004450020a202082280280438220800a00a288282042d08820a002088202204208a202088088282080413a20808a08028020a040620a00a208082282203fb0808828808220a0003eda08220828208a00a03e200228828028020a003d68a08800228a0020803ca828828008220208803bc28028020a20a08a203b1082022802080822803a6008220820a082088039a28208a00800a2802038f8228820200a088000381228a202088088282037600a20a08a200280003678a20808a20828228035c200808a20800220a034f00a08228828028a003440200a288082208200337a08a088202280202032a08028828208a20a0031e8a08020028a208080312a20028228020800a)) else (if i < 5 then (if i < 4 then 0x616a008088282288208060a08a08020228a202005ff0828008208820a0805f2828028008a20a00a05e620828208220008a205da8808220220a0820805cd820220a00a00a28805c128028820008a088205b60220a0020882082805aa208820a082280280059c28a20a08a008082205908220808a280082200583220a00028808228a057700a0082882022882056d0a08a00020208820055f208828828208220a055500a28020028a002005498a20828028220008053ba08808220a20a082052f288282288008002205228828228800a08a000517820228a200080280050b28008a20a00a280004fd8028a20a0882082804f1228220808820808204e400a20a082288202204d88200a00a2802022804cc800a08a08820008a04c020200828828200a204b40208a2802802882004a8a082008282202208049c08a08808220a2080 else 0x79f20208208820228a207940208808828200a200786808a28028028a208077c00a2080822820080076f8820808220a20a080763220828008a00a00a075628808228020a08a0074a8820228200208828073d828008a20208a280073120020a20a08a2002072582280208082288080719200a20a002088282070d28a00000a280282207028820a00a0880022006f3a20208828828208a06e820808a20028008a006da0a08a2082822822006cf808228800020a00a06c408228808028a002006b70a28828220020a0806ac8088202288202080069e28820208a20a08a006928028028820808a200686028208220800a288067a08220a2020802882066d8228a00a00a008280661200820a08a0882020656282200088288202006498a00a08a20028028063da202082208280202063020808a288082208206230a08228828228200) else (if i < 6 then 0x92a0a20208028828008091d820a08228008028a090f20a08a008282282209040808828008220a2008f7a00228800228a00a08eb00828028228820a008e08a00820208a2020008d2828828208220208a08c628020028a00a08a008bb0828020220008a2808ae808220a20808228808a228228800a002208208958228820a08208820088a028a200088280082087e08a20a00a280080208708220a088208282280865220808a20800200a085920a0822802822800084e0a00a288202088000841a00a08820028a202083408828828200a20a008288a08028020820a08081a220828228220808a080f08808220a008082208030028228a00a0022807f7808028820a08808807eb00228a202088208207de8208220a0882802807d1028220a08a20820207c628200808a280080207bb082020822882820007aca00a00a288282288 else 0xab0008a20208a2802800aa320820a08a20828200a9980208002288082200a8aa20208208828228a0a8000800a08028220820a740a00a08800228a200a67008828828208a00a0a5b08a20028008a20a00a4f82208280282208080a42a28800220a00a0820a3728828028200200820a298828220820a08a080a1e82022882020802800a1128208820a08a08020a068008a20800a2002809fa228220000a28808209ed20a20a080088282209e10a00a00a2082820809d4820808a08820228209ca00208820820208a009bd0a08228028028a2009b1208a20808220220809a508a28808220020a009988028828228a00a00098aa08820228820808a0980080202288202008209738808208a20a008280966028028a20208a208095a28208220808a0880094d8220220a082288200940228a00800a288280093528800208a0082022))) else (if i < 11 then (if i < 9 then (if i < 8 then 0xc3b20020a00a08a20820c2f8028220008a288080c22220a00a0822082820c1628800a00228828020c098820a08a088002280bfda2000882802820820bf120a00828008028a20be50a088208202282200bda808a20008200820a0bce08228828208200a00bc20a288202288002080bb5a08820028a2020880ba708828200a20a08a20b9c80280288208082200b90828228200808a0080b8408220a20808228020b778028a00a00a288080b6a228820a0880882020b5e28220208820828200b508a20a08a280200280b44220a08a2002022800b3900808a28808000a20b2e0200228828220a000b1f200a28828228820a0b1408208820220a20200b078808828208a208080af9a28028028a00a00a0aee20808228220808020ae28808020a20a082200ad5808208a00a00a2880ac828228020a08808820abc0228a00208828820 else 0xdc10808228220808a280db7800220200a0802880daa28028a00200a28820d9f0220820a08a080200d9222882020802882820d8608a20a00a08028020d798a20008a200282280d6d220800a08808220a0d5f20a08028828228a00d550800a208282088000d48a08a0082022822020d3e08028820008a00a00d318a28008028a202080d24a2082822022080880d1728808220820a08220d0a8820228a00a00a080cfe028228820808a0800cf320208a20200828800ce68208a202088280280cd8028a20a08a0082820ccc00220808a28808220cc002208082288202280cb3a00a00a2082802880ca820208208820020a20c9d02088288082088200c8fa08228028028220a0c8408800828228220800c788a28000220a20a000c6d228008228800a0080c6028828208820a00a00c540820208a202088280c47828208220a08a080) else (if i < 10 then 0xf4da20808200a20a0020f4028828228200200a20f338820228800a08a080f27820020a2020882880f1a28200a20808a28020f0e8028800a082208280f0322822080820880800ef720a20808228008220ee98a00a00a288082280edc020a08808820228a0ed020208820820208a20ec40a08a280280280200eb8a08a2082020820080ead00a28808020a20200ea08228828220a00a000e92a08828220820a0820e8708820228a20008800e7a8828208a00808a200e6e028028a20a0022080e6308028220808828800e558220a20a082208280e49208200a0082882820e3c28020a08a08820220e318a002088280280080e25820208a28028000a0e1820a00a20828228020e0d0008228808220a200e00a08208828220a0080df400a28028228820800de90a08800228a002080ddb820828208a20a0820dce20028008a20a08a2 else 0x10d408028828228a00a010c70a20828208820a0810bc208820028220208810af28800208a00a08a210a480280282202088201096828220220808a288108b00220820a0822802107e8228800a00a088281074208820800a080202106828a2020082880820105c8a20a08808028020104da20a08a208282082104120808a288082202010350a08220820228a001028a002288280288202101d08a08800220a202010108828828208020a081002028028028a20a08a0ff600820228220808a20feb8008220820a002280fdf808208a00a0082880fd228228820208a00820fc60208a202088088280fbb200220a08a2802000fae28a00808a20828020fa48200008a208082200f95a20a0822882802880f8900a00228808228820f7c0a08a088202282200f6f008828028208a20a0f6400a28000028a20a00f598820028228020808)) else (if i < 13 then (if i < 12 then 0x125e0a008288082288201250a08808820228a202124508820028208820a012398a28028008220a00122da20820228200008a122228808020a202082012148828220a00a00a281207828228820808208811fc20228a002088008211ef8208a2080822802811e2028a20a00a20808211d5282208088288082211ca0220a0802082820811bda00a00a28820228011b120a08a080202288011a50208828828008a201199200a28028020a202118d08a208282280208011808208808220a20a081173208828228a00800a116728028228800a00a0115c0800228a20208028114f828008a20a08a200114208008a20a08a208211368228220808828800112a220a00a082288200111d28a00200a280282211110820a08a088202081105820200028828208a10f820208a08028028a210ee0808a0002822022010e1800a28808220a208 else 0x13e5820008a08020228a13db20200808808200a213ce0a08828028028a2013c2808a20828208200813b608a20808220220a013aa8228820028a00a00139ca28808028820208a1391088202202202088213838828208820a082281378020028a20a08a000136c28228020808a280013608200a20a002288081353228a002008288282134728820a08a0082020133a0a20208828828208132d220808a28020028a132000a08a208280282213160008228808020a201308a08228808228800a12fc00228828228020a012f08808820228a2000812e3828020208a20a00a12d728008028820a088212cc0828208220800a2012c0808200a20208228812b328228200a00a088212a80220800a08a08820129b028a200088288282129000a00a08a200280212838820a082208280281276220808a08808220a126a2080822802822820) else (if i < 14 then 0x157228a202080088280015658a20808a280080281557a20a00a208082282154a20808828808220a2153f0a08220820208a001531a00a28028228020a152608a08820208a0020151a0828828008a20208150ba28028020a20a08a1501008282200208082214f58808220a2080820814e9828228a00800a20014dd28228820a002088014d10028a2020882880814c4208a20a08a20028014b708220a088208282214ab8220808a28800220149ea00a082280280288149300200a288282008214870a00a088202288201479208028828208a20a146e08a08028020a208014628a200282282208001455a28808220a00a080144820828228a00a0022143c0828008820a08a0814308002282202088288142520208200a088280214188028a20208a20820140c220220808a28008213ff20820a082288282013f18a00a00a08828228 else 0x167f0000000000002000167028828228820a08a016638820228a200088281657028208820a00a280164c08008a20a008208216408228220008a208081633200a20a082088282162720200a00a2882022161c8800808a088200281610a00208820828200a160320a082280280288215f70a0822080822822015eb808a08808220220815df08028028228a00a015d20a28800228820a0815c7808020228820208815b920828208a20a00a215ad8028028220208a2015a1820228200808a088159508020a202082288215888220a00800a28828157d228800a082008202))))
private def withinPeriod (n : ℕ) : ℕ :=
  let word := (packet (n/2048) >>> (80*((n%2048)/64)))%(2^80)
  (word >>> 64)+pop (word%(2^(n%64+1)))

def wheel (n : ℕ) : ℕ := (n/30030)*5760+withinPeriod (n%30030)
private def check (r : ℕ) : Bool :=
  wheel (r+1) == wheel r + (if cop (r+1) then 1 else 0)

private def valid (lo len : ℕ) : Prop := (List.range' lo len).all check=true
private theorem glue {lo a b : ℕ} (u : valid lo a) (v : valid (lo+a) b) : valid lo (a+b) := by
  unfold valid at *
  rw [← List.range'_append_1,List.all_append,u,v]
  rfl

private theorem halve (lo n : ℕ) (h : valid lo (n/2))
    (k : valid (lo+n/2) (n-n/2)) : valid lo n := by
  simpa only [show n/2+(n-n/2)=n by omega] using glue h k
private def covered (lo hi : ℕ) : Prop := ∀ j, lo≤j → j < hi → check j=true
private theorem checked {lo hi : ℕ} (h : valid lo (hi-lo)) : covered lo hi := by
  intro j lower upper
  exact List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨lower,by omega⟩)
private theorem joinCoverage {lo mid hi : ℕ} (l : covered lo mid) (r : covered mid hi) :
    covered lo hi := by
  intro j lower upper
  by_cases h : j < mid
  · exact l j lower h
  · exact r j (by omega) upper

private theorem c0 : covered 0 938 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c938 : covered 938 1876 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c1876 : covered 1876 2814 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c2814 : covered 2814 3753 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c3753 : covered 3753 4691 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c4691 : covered 4691 5630 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c5630 : covered 5630 6568 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c6568 : covered 6568 7507 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c7507 : covered 7507 8445 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c8445 : covered 8445 9384 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c9384 : covered 9384 10322 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c10322 : covered 10322 11261 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c11261 : covered 11261 12199 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c12199 : covered 12199 13138 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c13138 : covered 13138 14076 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c14076 : covered 14076 15015 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c15015 : covered 15015 15953 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c15953 : covered 15953 16891 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c16891 : covered 16891 17829 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c17829 : covered 17829 18768 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c18768 : covered 18768 19706 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c19706 : covered 19706 20645 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c20645 : covered 20645 21583 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c21583 : covered 21583 22522 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c22522 : covered 22522 23460 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c23460 : covered 23460 24399 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c24399 : covered 24399 25337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c25337 : covered 25337 26276 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c26276 : covered 26276 27214 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c27214 : covered 27214 28153 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c28153 : covered 28153 29091 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem c29091 : covered 29091 30030 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 0 30030 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage c0 c938) (joinCoverage c1876 c2814)) (joinCoverage (joinCoverage c3753 c4691) (joinCoverage c5630 c6568))) (joinCoverage (joinCoverage (joinCoverage c7507 c8445) (joinCoverage c9384 c10322)) (joinCoverage (joinCoverage c11261 c12199) (joinCoverage c13138 c14076)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage c15015 c15953) (joinCoverage c16891 c17829)) (joinCoverage (joinCoverage c18768 c19706) (joinCoverage c20645 c21583))) (joinCoverage (joinCoverage (joinCoverage c22522 c23460) (joinCoverage c24399 c25337)) (joinCoverage (joinCoverage c26276 c27214) (joinCoverage c28153 c29091)))))

private theorem wheel_shift (q r : ℕ) : wheel (30030*q+r)=q*5760+wheel r := by
  simp [wheel,Nat.mul_add_div (by decide : 0<30030),Nat.add_mul,Nat.add_assoc]

private theorem cop_shift (q r : ℕ) : cop (30030*q+r)=cop r := by
  have m2 : (30030*q+r)%2 = r%2 := by rw [show 30030*q=2*(15015*q) by ring,Nat.mul_add_mod]
  have m3 : (30030*q+r)%3 = r%3 := by rw [show 30030*q=3*(10010*q) by ring,Nat.mul_add_mod]
  have m5 : (30030*q+r)%5 = r%5 := by rw [show 30030*q=5*(6006*q) by ring,Nat.mul_add_mod]
  have m7 : (30030*q+r)%7 = r%7 := by rw [show 30030*q=7*(4290*q) by ring,Nat.mul_add_mod]
  have m11 : (30030*q+r)%11 = r%11 := by rw [show 30030*q=11*(2730*q) by ring,Nat.mul_add_mod]
  have m13 : (30030*q+r)%13 = r%13 := by rw [show 30030*q=13*(2310*q) by ring,Nat.mul_add_mod]
  simp only [cop,m2,m3,m5,m7,m11,m13]

theorem wheel_succ (t : ℕ) :
    wheel (t+1)=wheel t+(if cop (t+1) then 1 else 0) := by
  let r := t%30030
  let q := t/30030
  have split : t=30030*q+r := (Nat.div_add_mod t 30030).symm
  have item := allrows r (Nat.zero_le _) (Nat.mod_lt t (by decide))
  have step : wheel (r+1)=wheel r+(if cop (r+1) then 1 else 0) := beq_iff_eq.mp item
  rw [split,Nat.add_assoc,wheel_shift,wheel_shift,cop_shift,step,Nat.add_assoc]

private theorem cop_iff (n : ℕ) : cop n=true ↔ ∀ p ∈ Nat.primesLE 13, ¬ p ∣ n := by
  have ps : Nat.primesLE 13 = ({2,3,5,7,11,13} : Finset ℕ) := by decide +kernel
  rw [ps]
  simp [cop,Nat.dvd_iff_mod_eq_zero]

theorem count_rough (t : ℕ) :
    ((Icc 1 t).filter (fun n => ∀ p ∈ Nat.primesLE 13, ¬ p ∣ n)).card = wheel t := by
  induction t with
  | zero => decide +kernel
  | succ n ih =>
    have interval : Icc 1 (n+1) = insert (n+1) (Icc 1 n) := by
      ext k
      simp only [mem_Icc,mem_insert]
      omega
    have fresh : n+1 ∉ Icc 1 n := by simp
    rw [interval,Finset.filter_insert,wheel_succ,←ih]
    by_cases hp : ∀ p ∈ Nat.primesLE 13, ¬p ∣ n+1
    · rw [if_pos hp,(cop_iff _).mpr hp]
      exact Finset.card_insert_of_notMem (fun mem => fresh (Finset.mem_filter.mp mem).1)
    · have no : cop (n+1)=false := Bool.eq_false_iff.mpr (mt (cop_iff _).mp hp)
      rw [if_neg hp,no]
      simp

end ShortPeriod30030


/- Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace FastDenseA100

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


private def packet (i : ℕ) : ℕ := (if i < 7 then (if i < 3 then (if i < 1 then 0x3ab60e119d9b6d2b63403944308218d32405aae037a522434c0a262c7570360b01689d1784d8c180345ada9c22287ce24050328618302abcad593d2030c2770494d45aa5a8602f214089851b7e3556002d62e1568bf88056a0702b99c742f3ad40648d102a0c41e22a6502b962402838dea735ca89501190266f8246c44cbf10b43024b307a4c570c944ab2022f02cdcdb50238f12c0211c383dc8219f6264e01f44c58b42aa71c8b5a01d64d33f3243e88518d01b999eb813c26c73811019ea0e3266581d892d2017b87588f9265aefb720162468c83e5081a96540142ef17c19b7171582101224f8cbcc8b37ac18c010454bf11453a2b4cb800e13a13f666e944fd2e00c1f8a154039ff0a3d9009f554c2ade2dade356007d56a61e78bd92676a0059a559dd3bd3d30ce600319eeda6eaf31e4fd50000f93ddbb67eefdffe else (if i < 2 then 0x6e2a1aab3e1522a44b506cc155941180896a81606b0b1474266d75888980693f40c0fd888a13367068030831c4901c11218066ae8021d1461b0180d064c5c788582a4742d9f0635a08ac312424892d5061f073110366302a4b006041b6614e808d83c6a05ebc476e0092ca50a6105ce4a84d62d2a8b935605b3c319653818c126cd059b91500ec0f60c2e06057e15a9d8d2182f54f0056a0931a610461a818205518bc61a44c88c27220536c760421da13859b20520104ac2b029c3d3000506a508e9861b26568204ee818992787024225d04d24c8ed84446e5c16c04bbb430300a25c31934049de34730e982b129e904831006c514dc3dcb1404672e644e1194e3471a044f2902ac8f81c5680a04301cb59861572ae6c3041838b14873440319e003fc32c8231e685da12703e5105574a88388099a03ca947a44d060391a67 else 0x9f0b7484c511415c01609d61a8596b4a171c00e09c12d050c8b409530c009a8197c9080613a698c098ed9364b110a8445650976866253324449301d095ab2f02e6f10089770094214780a82150eaae109291483817d0c62a4720913c280308cf932444108fe912809c930700d0608e5e0bb5812248c845908c938db21462d1ccc9208afc1834c29426c92b3089804002a54cd032bd3087d7e47c008a48aa32e08690c518403e11464280856903c80a0805a42c40841c525021058098e490827076a4626448f309c080d6b2520cf8291bc0807f33730adc5093211c107dd328a0cb018b1e12007bfa3d629317a25562c07aa022439c28252c20b0790750b88570ce409c407791063206c478c980b076250a0560e57012ca8074c840a61d07801915607347e08150c826b362007170ad654be00673ca306ff0ca5111855624559)) else (if i < 5 then (if i < 4 then 0xcd75a952b004238a29c0cc230860982146a41a90caa09532438eb84908c0c9728221601d91888810c81c45009c1612370160c6a04484ac5b842d1520c542145352a53c102600c3d5e80848b24268a1a0c20612c29522ec79b2c0c0ab618c242e1ca01800bf3b2f000a50c4409b30bdd230686435c3148060bc11aecd9f8078851140bac0c05b083829632030b9b02808f29811480420b81391b8914542e144d0b658ca9445083dddc830b515014462046a0a3520b37d11286981d9228d50b20442e88092671216c0b0ac88a3421c16342480af1d2692cf1064001da0ada898452e13c015aa00ac229ca1712421c40b60aad4872222704a918880a9923548144410652a10a866061d12c829004060a69a851a1197b5528e30a4f471023aae20ec48b0a335c2033c078e91eb40a20220891108190d51c0a08a1022e8a89109579 else 0xfb843047663443486d20fa66028088a811e1b000f9312a5510c8c02022c0f770ac891af329768430f620890ae31701848510f4da5208a1206a1ca280f3219e99312448f94a10f1963544a82996538180f02f30800c84c2ac2c50eed22860514324b021e0ed5cac44930a9342e040ec1d1800300025c605f0eab3101326344489b050e9393030404e496acac0e8018010ca0c2543c220e690472a44ad18459c00e512a2d9990a44135120e39ce4bc11c093338000e25062c8203074461540e0b319473a1482016f90df3b6c2644aa60269100ddcf9953002096585800dc1d14c62c8d991c3820dac206c0ee4203a500a0d9145c2ec1c1b220ccd0d7707e91cf0071849c80d608c30aaf430c54a000d4c1148b010c1853c220d361ac2144a1d1c26800d1f001e821b9016f3600d066e2e8c05a928c0540cef270445ada2c14a02) else (if i < 6 then 0x1289458300a4e80050c912745e009b10131a8508125fb0994855002a489112470eb264624015843712348051400a1968928a121c9160a29c4485981712074e0288dc9740601011f12d140009fa811ca411d681e5312936166d4811c4418240017e28070411ad258a73380c109415119b11740005c14502431187222442481990c8a311704ac18069a41a51521159aed22c04239040a6113e5f583b28a342cc1011259c9ba22404cd0878110b8cbb115a89c0641510f382a014a717d880e110dfd122480cb415402110c42a4f4cf12d18061610ab8b0844aa0a6274e91099116480b800322350108489a2d92078020740106e00d0470862cc392a1058083460e442811ad31041b424a48aa8268162102c04c505e00560a24e10148c594005f2a50e280ffddaa01c6043284e440fe35529094232cec38c0fd1a1c836400401f100 else 0x154b8130c418eb9c2182153818204627062818a1151fb02c068d30997286150902615b108ce1821a14f3089255945026206714e14c9520184006ac0114cb4582e2412e4a144114b53303211c248ac1a8149eb2523081c168930a1483c6448743c4b7d041146b3c821851a278231c1458200599016194288c144552a9009a444209061431102f01e24a018454141d1a6165064c0710101401d1e5528e4c2c027313eb811449473813911113d5382a4a00b3c0866413be638c382c1231404713a5c3908ec1225ca988138d500229b20ea3970c1377003930646141d8171362c8907244460c8522134f841a8a05a12820d0133806c6c3412250b330131f0e1d8438a8a5284b130757008532344c82da12f1a11110813ae4503512df02180208849341b612c80196184788e8858a12b3a046a31781210192129c342d02a09d0b406c))) else (if i < 10 then (if i < 8 then 0x180d02c18a6c0341414417fd008d24240346140117e54a79b0a00508ce1a17cf88a1b3572000949817bc02c242484b10613417a60a8034aa1dd0069817968514240288082324177f58c2c1e4370116201767620e5c32d2b54001174d4869b242a46a4acc17392d9498517680010017233151512a86044c2a170d2a04060d934cb81116f760040b96e18e21a016e156c641181851842a16c8a0cf4116e2a2660116b55130304a120242ca169d318119a50c4cc8e4168392989600e8552d9c166c4243706a130d156016526134204eacba4b11163e4aa0412038b0322616282149d40980d2108f160f0e842afad040471515f95c2da8a01485109115e38121417c4100a8bb15d0014212c0c781246815bca43206846022d10315a3602a11d10e638678158b20d1ec17116452841579020919290540a20d156250249a370684c158 else (if i < 9 then 0x1ab8a00b01a5404212f51aa48801c1162a8c98a01a8fc111106515d83a001a7ea10421018422f0051a68140c9129080a966e1a52054248a32a7548a01a3b810494b29344e60a1a2475a420e0108d113c1a0e3499a440c6c9081819f6b9602a4d049409a919e146404891518968a419cf1a8448599a01410019bc8404e41038c6168019a64c54342111762091198a01bb921662a38b7119768220326a4518188a195f3220486e14e5a148194a715021138534601419344c4202889c0b653219254008a80cc061400a19118c640350311c088518ff1818d210208b005918e388e94452ab86b09718c9b221542a5861a39318b6531c86030130808618a14a2a81803d80b450188e65028509494118281877d25508a8165a80511865080619704008d584184c0fa0851a8347948a183b20250a2804142a43182053566841d82659c1 else 0x1d6807184210d1841a211d530e2655410c42b0481d3e08c1e90a007228651d2c80240fe2070808881d14441b504538e0c4b41cfe0b19d54080141d921ce752c222889b8934881cd52060069c002168561cbe6647022591ba90081ca8099255073084642c1c900e580b1a8204ae931c7ca901c306162045601c681252b060091414a91c51c15072c550d00b281c3f4602ad0629108a001c2c240154048c70e2181c15e34769a00a10182a1bfe94ad3858022640591beb34050062460a138c1bd53d0074202d9859201bbbd94342a394d130911ba8042ec142401829921b8d086c4aacb06bf20a1b790e98210758a024a01b5f8935a391c5326c401b4b488822821a2390cc1b3622833434a809c1031b1d628426c38e518f201b089520af00858482321af674809c30231140401ae14010803d5a260ce41acd06180072c45c09c2)) else (if i < 12 then (if i < 11 then 0x20121ad51590303a80421ffbad2588570083d0141fe81880c544624841191fd50231204986948e101fc10214ab53a81181201faa724f9810021163621f9a08d1082049c0120c1f83d4703c200308e5071f6ea182d9d0040a45a01f59142307726949a0001f3f5135780e4ba1888a1f29822064921c9632a41f1700ee52800a21240c1f02e902cc00c8714a041ee886543d7920486b901ecf088ca8f132091f941ebc35601212418c30821ea510c32282c92d311a1e92740603048432d0601e7a1c8b1cdd0290003e1e67220f64a1a30044041e4f59389298a46885811e3c542ec142086400b01e2704a1721888d780111e11530068424b8983921e009032040214170a211deb604cda310420a5121dd88a84602818a046491dbc196cb42307066bc31da761b411300aa68a041d90bcf04506460144831d7b2a440cc0d04c13a1 else 0x22ab48260a0540d037612299200a064f0518414422874025015c0488c0782272491b70042b406a80225bc86db4318008a2942249111710434c4a008422342a30953088027921222160301e2cc0082542220692764883108ec17721ef2a608ab410a9a26221d9c00025b851741c0b21c4c510a918d540224821ac64166880426b1995219406d821108a4b483f2181e10324011f40318021701048c1c01910803321630481864402802208214ea0109d198914168821364158116187642dc8211f383b8b85404b184021098258c61c0d03818920f69844260c44a4b80020e42750404648a4620020d03022c42c2513444820b4a59d091e2ae0266520a30b1c0a803324000c209028805bb0440443442079346396142158108e2064b1012c0c4a009ac9204dc02244cf04932133203d102801b0118a05142028c708e18020244ce1) else (if i < 13 then 0x2551ea8a1409f0a30846253c0764381220242716252930102235480540bc250fa8e04458c44ab1ba24fb70903428039c20c124e594104c48912ac8a624d232821e302303502024c008c104130382544624ad8065bc88330021022497418070757045806924862813f0020c408508247113b4124140211ea8245ac10640161c32aab424490a0708013418121a2434a744841043c064e024214d2192900220c819240a31322b056200cdc823f4135b0004665124a623e010670ca94880930223c6d62cc9904907794023b114e8058818883664239d6702188a01814a4923849d880a43d43081c72372310940a3008c07a0235a8a883266264d7104234b11820c208c40028323360478285f88029054231f02e21c5da022a12c230b4ad0d0015035142822ef1e8525a34252cd9322db9809330018a3812922c09eda4310215b88b8 else 0x256900c0898500c30720))))


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


private def radical : ℕ := 61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210

private def light (n : ℕ) : Bool :=
  if n≤17 then decide n.Prime else n.gcd 355687428096000 == 1

private theorem light_ok {n : ℕ} (hn : n≤316) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 17 = 355687428096000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 17 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤316 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 39 := by unfold smallValid; decide +kernel

private theorem sp39 : smallValid 39 40 := by unfold smallValid; decide +kernel

private theorem sp79 : smallValid 79 39 := by unfold smallValid; decide +kernel

private theorem sp118 : smallValid 118 40 := by unfold smallValid; decide +kernel

private theorem sp158 : smallValid 158 39 := by unfold smallValid; decide +kernel

private theorem sp197 : smallValid 197 40 := by unfold smallValid; decide +kernel

private theorem sp237 : smallValid 237 40 := by unfold smallValid; decide +kernel

private theorem sp277 : smallValid 277 40 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤316) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 317 := (joinSmall (lo:=0) (a:=158) (b:=159) (joinSmall (lo:=0) (a:=79) (b:=79) (joinSmall (lo:=0) (a:=39) (b:=40) sp0 sp39) (joinSmall (lo:=79) (a:=39) (b:=40) sp79 sp118)) (joinSmall (lo:=158) (a:=79) (b:=80) (joinSmall (lo:=158) (a:=39) (b:=40) sp158 sp197) (joinSmall (lo:=237) (a:=40) (b:=40) sp237 sp277)))
  have good : (List.range 317).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 100000) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 316 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 316 := by
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



private theorem d0 : covered 0 833 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d833 : covered 833 1667 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d1667 : covered 1667 2501 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d2501 : covered 2501 3335 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d3335 : covered 3335 4168 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d4168 : covered 4168 5002 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d5002 : covered 5002 5836 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d5836 : covered 5836 6670 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d6670 : covered 6670 7503 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d7503 : covered 7503 8337 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d8337 : covered 8337 9171 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d9171 : covered 9171 10005 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d10005 : covered 10005 10838 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d10838 : covered 10838 11672 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d11672 : covered 11672 12506 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d12506 : covered 12506 13340 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d13340 : covered 13340 14173 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d14173 : covered 14173 15007 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d15007 : covered 15007 15841 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d15841 : covered 15841 16675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d16675 : covered 16675 17508 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d17508 : covered 17508 18342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d18342 : covered 18342 19176 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d19176 : covered 19176 20010 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d20010 : covered 20010 20843 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d20843 : covered 20843 21677 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d21677 : covered 21677 22511 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d22511 : covered 22511 23345 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d23345 : covered 23345 24178 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d24178 : covered 24178 25012 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d25012 : covered 25012 25846 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem d25846 : covered 25846 26680 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 0 26680 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage d0 d833) (joinCoverage d1667 d2501)) (joinCoverage (joinCoverage d3335 d4168) (joinCoverage d5002 d5836))) (joinCoverage (joinCoverage (joinCoverage d6670 d7503) (joinCoverage d8337 d9171)) (joinCoverage (joinCoverage d10005 d10838) (joinCoverage d11672 d12506)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage d13340 d14173) (joinCoverage d15007 d15841)) (joinCoverage (joinCoverage d16675 d17508) (joinCoverage d18342 d19176))) (joinCoverage (joinCoverage (joinCoverage d20010 d20843) (joinCoverage d21677 d22511)) (joinCoverage (joinCoverage d23345 d24178) (joinCoverage d25012 d25846)))))

theorem fast_correct (n : ℕ) (bound : n ≤ 100000) : fast n = Nat.primeCounting n := by
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
      · have ix := index_bound (show n≤100000 by omega)
        have h := beq_iff_eq.mp (allrows (index n) (Nat.zero_le _) ix)
        change raw (index n+1) = raw (index n) + (if quick (number (index n)) then 1 else 0) at h
        rw [whose] at h
        simp only [fast,e,h,unchanged]
        by_cases hp : (n+1).Prime
        · simp [hp,(quick_ok bound).mpr hp,Nat.add_right_comm]
        · simp [hp,mt (quick_ok bound).mp hp]
def prime (n : ℕ) : Bool := quick n
theorem prime_ok (n : ℕ) (hn : n≤100000) : prime n=true ↔ n.Prime := quick_ok hn
end FastDenseA100

end Sieve555157672301From131To311

open Sieve555157672301From131To311
open Finset
namespace IndexedSlicedSieveA26From32To64

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
  | p :: ps, t => if p=13 then ShortPeriod30030.wheel t else if t < p then (if t=0 then 0 else 1) else
      if t < (p+1)^2 ∧ t ≤ 100000 then 1 + table t - table p else
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
    (pos : 0 < p) (cap : 100000 ≤ bound) : ∀ t,
    (p::ps).foldr advance id t = evalPhi tab (p::ps) t := by
  intro t
  by_cases hbase : p=13
  · subst p
    have val : (13::ps).foldr advance id t = ShortPeriod30030.wheel t := by
      rw [←lst]
      exact (legendre_range 13 t).trans (ShortPeriod30030.count_rough t)
    simpa [evalPhi] using val
  by_cases sm : t < p
  · simp [List.foldr_cons,advance,evalPhi,hbase,sm]
  · by_cases short : t < (p+1)^2 ∧ t ≤ 100000
    · have h := square_cut pos (by omega : p ≤ t) short.1
      rw [lst] at h
      rw [evalPhi,if_neg hbase,if_neg sm,if_pos short,ok t (by omega),ok p (by omega)]
      omega
    · simp only [List.foldr_cons,advance,evalPhi,if_neg hbase,if_neg sm,if_neg short,prev]

private theorem merge_filter (f : ℕ → Bool) (lo a b : ℕ) (l r : List ℕ)
    (hl : (List.range' lo a).filter f = l) (hr : (List.range' (lo+a) b).filter f = r) :
    (List.range' lo (a+b)).filter f = l++r := by
  rw [←List.range'_append_1,List.filter_append,hl,hr]

private theorem eval_delta (tab : ℕ → ℕ) (ps : List ℕ) (p n q old dec ans : ℕ)
    (notWheel : p≠13) (le : p ≤ n) (sq : (p+1)^2 ≤ n) (div : n/p = q)
    (base : evalPhi tab ps n = old) (cut : evalPhi tab ps q = dec) (sub : old-dec=ans) :
    evalPhi tab (p::ps) n = ans := by
  rw [evalPhi,if_neg notWheel,if_neg (not_lt.mpr le),if_neg (fun h => (not_lt.mpr sq) h.1),div,base,cut,sub]

private theorem agree_range {bound : ℕ} (table : ℕ → ℕ)
    (ok : ∀ t, t ≤ bound → table t = Nat.primeCounting t)
    (y : ℕ) (cap : 100000 ≤ bound) :
    ∀ t, (((List.range (y+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id) t =
      evalPhi table ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse t := by
  induction y with
  | zero => simp [List.range_succ,evalPhi]
  | succ n ih =>
    by_cases hp : (n+1).Prime
    · have row : ((List.range (n+1+1)).filter (fun p => decide p.Prime)).reverse =
          (n+1) :: ((List.range (n+1)).filter (fun p => decide p.Prime)).reverse := by
        rw [List.range_succ (n:=n+1),List.filter_append,List.reverse_append]
        simp [hp]
      rw [row]
      exact refine_row table ok _ row ih (by omega) cap
    · have row : ((List.range (n+1+1)).filter (fun p => decide p.Prime)).reverse =
          ((List.range (n+1)).filter (fun p => decide p.Prime)).reverse := by
        rw [List.range_succ (n:=n+1),List.filter_append,List.reverse_append]
        simp [hp]
      rw [row]
      exact ih



private abbrev tab := FastDenseA100.fast
private abbrev F := evalPhi tab
private abbrev prime := FastDenseA100.prime
private theorem prime_ok (n : ℕ) (h : n≤100000) : prime n=true ↔ n.Prime := FastDenseA100.prime_ok n h

private def rankedPhi (table : ℕ → ℕ) : ℕ → List ℕ → ℕ → ℕ
  | _, [], t => t
  | a, p::ps, t =>
    if p=13 then ShortPeriod30030.wheel t
    else if t < p then (if t=0 then 0 else 1)
    else if t < (p+1)^2 ∧ t ≤ 100000 then 1+table t-a
    else rankedPhi table (a-1) ps t - rankedPhi table (a-1) ps (t/p)

private theorem ranked_range {b : ℕ} (table : ℕ → ℕ)
    (ok : ∀ n, n≤b → table n=Nat.primeCounting n) (y : ℕ) (yb : y≤b) :
    ∀ t, evalPhi table ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse t =
      rankedPhi table (Nat.primeCounting y) ((List.range (y+1)).filter (fun p => decide p.Prime)).reverse t := by
  induction y with
  | zero => simp [List.range_succ,evalPhi,rankedPhi]
  | succ n ih =>
    have prev := ih (by omega)
    have succCount : Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0) :=
      Nat.count_succ Nat.Prime (n+1)
    by_cases hp : (n+1).Prime
    · have row : ((List.range (n+1+1)).filter (fun p => decide p.Prime)).reverse =
          (n+1) :: ((List.range (n+1)).filter (fun p => decide p.Prime)).reverse := by
        rw [List.range_succ (n:=n+1),List.filter_append,List.reverse_append]
        simp [hp]
      have grade : Nat.primeCounting (n+1)=Nat.primeCounting n+1 := by rw [succCount,if_pos hp]
      have value : table (n+1)=Nat.primeCounting n+1 := (ok _ yb).trans grade
      intro t
      rw [row,grade]
      simp only [evalPhi,rankedPhi,Nat.add_sub_cancel,prev,value]
    · have row : ((List.range (n+1+1)).filter (fun p => decide p.Prime)).reverse =
          ((List.range (n+1)).filter (fun p => decide p.Prime)).reverse := by
        rw [List.range_succ (n:=n+1),List.filter_append,List.reverse_append]
        simp [hp]
      rw [row,succCount,if_neg hp,Nat.add_zero]
      exact prev

private abbrev R := rankedPhi tab
private def resumeRank (base : List ℕ) (start : ℕ) : ℕ → List ℕ → ℕ → ℕ
  | _, [], _ => start
  | a, p::ps, t =>
    if p=13 then ShortPeriod30030.wheel t
    else if t < p then (if t=0 then 0 else 1)
    else if t < (p+1)^2 ∧ t ≤ 100000 then 1+tab t-a
    else resumeRank base start (a-1) ps t - R (a-1) (ps++base) (t/p)

private theorem resume_correct (portion base : List ℕ) (baseRank t start : ℕ) (old : R baseRank base t=start) :
    R (baseRank+portion.length) (portion++base) t = resumeRank base start (baseRank+portion.length) portion t := by
  induction portion with
  | nil => simpa [resumeRank] using old
  | cons p ps ih =>
    simp only [List.cons_append,List.length_cons,Nat.add_succ,rankedPhi,resumeRank,Nat.succ_sub_one,ih]

private theorem continue_at {portion base whole : List ℕ} {t start answer baseRank rank : ℕ}
    (same : portion++base=whole) (grade : baseRank+portion.length=rank)
    (old : R baseRank base t=start) (checked : resumeRank base start rank portion t=answer) :
    R rank whole t=answer := by
  subst whole
  subst rank
  exact (resume_correct portion base baseRank t start old).trans checked

private def sa0 : List ℕ := []
private def sc8 : List ℕ := [19,17,13,11,7,5,3,2]
private def sa8 : List ℕ := sc8++sa0
private def sc16 : List ℕ := [53,47,43,41,37,31,29,23]
private def sa16 : List ℕ := sc16++sa8
private def sc24 : List ℕ := [89,83,79,73,71,67,61,59]
private def sa24 : List ℕ := sc24++sa16
private def sc32 : List ℕ := [131,127,113,109,107,103,101,97]
private def sa32 : List ℕ := sc32++sa24
private def sc33 : List ℕ := [137]
private def sc34 : List ℕ := [139,137]
private def sc35 : List ℕ := [149,139,137]
private def sc36 : List ℕ := [151,149,139,137]
private def sc37 : List ℕ := [157,151,149,139,137]
private def sc38 : List ℕ := [163,157,151,149,139,137]
private def sc39 : List ℕ := [167,163,157,151,149,139,137]
private def sc40 : List ℕ := [173,167,163,157,151,149,139,137]
private def sa40 : List ℕ := sc40++sa32
private def sc41 : List ℕ := [179]
private def sc42 : List ℕ := [181,179]
private def sc43 : List ℕ := [191,181,179]
private def sc44 : List ℕ := [193,191,181,179]
private def sc45 : List ℕ := [197,193,191,181,179]
private def sc46 : List ℕ := [199,197,193,191,181,179]
private def sc47 : List ℕ := [211,199,197,193,191,181,179]
private def sc48 : List ℕ := [223,211,199,197,193,191,181,179]
private def sa48 : List ℕ := sc48++sa40
private def sc49 : List ℕ := [227]
private def sc50 : List ℕ := [229,227]
private def sc51 : List ℕ := [233,229,227]
private def sc52 : List ℕ := [239,233,229,227]
private def sc53 : List ℕ := [241,239,233,229,227]
private def sc54 : List ℕ := [251,241,239,233,229,227]
private def sc55 : List ℕ := [257,251,241,239,233,229,227]
private def sc56 : List ℕ := [263,257,251,241,239,233,229,227]
private def sa56 : List ℕ := sc56++sa48
private def sc57 : List ℕ := [269]
private def sc58 : List ℕ := [271,269]
private def sc59 : List ℕ := [277,271,269]
private def sc60 : List ℕ := [281,277,271,269]
private def sc61 : List ℕ := [283,281,277,271,269]
private def sc62 : List ℕ := [293,283,281,277,271,269]
private def sc63 : List ℕ := [307,293,283,281,277,271,269]

private theorem transfer {ps : List ℕ} {a p q origin removed step total : ℕ}
    (ne : p≠13) (old : R a ps 555157672301=origin-removed) (part : R a ps q=step)
    (div : 555157672301/p=q) (le : p≤555157672301) (sq : (p+1)^2≤555157672301) (sum : removed+step=total) :
    R (a+1) (p::ps) 555157672301=origin-total := by
  have notShort : ¬ (555157672301 < (p+1)^2 ∧ 555157672301 ≤ 100000) := fun h => (not_lt.mpr sq) h.1
  simp only [R] at old part ⊢
  simp only [rankedPhi,if_neg ne,if_neg (not_lt.mpr le),if_neg notShort,
    Nat.add_sub_cancel,div,old,part,Nat.sub_sub,sum]

private def ps32 : List ℕ := [131,127,113,109,107,103,101,97,89,83,79,73,71,67,61,59,53,47,43,41,37,31,29,23,19,17,13,11,7,5,3,2]
private def origin : ℕ := R 32 ps32 555157672301
private theorem v32 : R 32 ps32 555157672301=origin-0 := by rw [Nat.sub_zero]; rfl

private def ps33 : List ℕ := 137::ps32

private theorem h33_8 : R 8 sa8 4052245783=693031376 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=4052245783) (start:=4052245783) rfl rfl rfl (by decide +kernel)
private theorem h33_16 : R 16 sa16 4052245783=551457891 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=4052245783) (start:=693031376) rfl rfl h33_8 (by decide +kernel)
private theorem h33_24 : R 24 sa24 4052245783=492638063 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=4052245783) (start:=551457891) rfl rfl h33_16 (by decide +kernel)
private theorem c33 : R 32 ps32 4052245783=457904438 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=4052245783) (start:=492638063) rfl rfl h33_24 (by decide +kernel)
private theorem v33 : R 33 ps33 555157672301=origin-457904438 :=
  transfer (a:=32) (p:=137) (origin:=origin) (removed:=0) (by decide) v32 c33 rfl (by decide) (by decide) rfl

private def ps34 : List ℕ := 139::ps33

private theorem h34_8 : R 8 sa8 3993940088=683059696 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=3993940088) (start:=3993940088) rfl rfl rfl (by decide +kernel)
private theorem h34_16 : R 16 sa16 3993940088=543523214 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=3993940088) (start:=683059696) rfl rfl h34_8 (by decide +kernel)
private theorem h34_24 : R 24 sa24 3993940088=485549822 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=3993940088) (start:=543523214) rfl rfl h34_16 (by decide +kernel)
private theorem h34_32 : R 32 sa32 3993940088=451315863 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=3993940088) (start:=485549822) rfl rfl h34_24 (by decide +kernel)
private theorem c34 : R 33 ps33 3993940088=448021096 :=
  continue_at (portion:=sc33) (base:=sa32) (rank:=33) (baseRank:=32) (t:=3993940088) (start:=451315863) rfl rfl h34_32 (by decide +kernel)
private theorem v34 : R 34 ps34 555157672301=origin-905925534 :=
  transfer (a:=33) (p:=139) (origin:=origin) (removed:=457904438) (by decide) v33 c34 rfl (by decide) (by decide) rfl

private def ps35 : List ℕ := 149::ps34

private theorem h35_8 : R 8 sa8 3725890418=637216767 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=3725890418) (start:=3725890418) rfl rfl rfl (by decide +kernel)
private theorem h35_16 : R 16 sa16 3725890418=507045157 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=3725890418) (start:=637216767) rfl rfl h35_8 (by decide +kernel)
private theorem h35_24 : R 24 sa24 3725890418=452962903 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=3725890418) (start:=507045157) rfl rfl h35_16 (by decide +kernel)
private theorem h35_32 : R 32 sa32 3725890418=421025928 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=3725890418) (start:=452962903) rfl rfl h35_24 (by decide +kernel)
private theorem c35 : R 34 ps34 3725890418=414944023 :=
  continue_at (portion:=sc34) (base:=sa32) (rank:=34) (baseRank:=32) (t:=3725890418) (start:=421025928) rfl rfl h35_32 (by decide +kernel)
private theorem v35 : R 35 ps35 555157672301=origin-1320869557 :=
  transfer (a:=34) (p:=149) (origin:=origin) (removed:=905925534) (by decide) v34 c35 rfl (by decide) (by decide) rfl

private def ps36 : List ℕ := 151::ps35

private theorem h36_8 : R 8 sa8 3676540876=628776810 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=3676540876) (start:=3676540876) rfl rfl rfl (by decide +kernel)
private theorem h36_16 : R 16 sa16 3676540876=500329320 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=3676540876) (start:=628776810) rfl rfl h36_8 (by decide +kernel)
private theorem h36_24 : R 24 sa24 3676540876=446963466 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=3676540876) (start:=500329320) rfl rfl h36_16 (by decide +kernel)
private theorem h36_32 : R 32 sa32 3676540876=415449434 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=3676540876) (start:=446963466) rfl rfl h36_24 (by decide +kernel)
private theorem c36 : R 35 ps35 3676540876=406698182 :=
  continue_at (portion:=sc35) (base:=sa32) (rank:=35) (baseRank:=32) (t:=3676540876) (start:=415449434) rfl rfl h36_32 (by decide +kernel)
private theorem v36 : R 36 ps36 555157672301=origin-1727567739 :=
  transfer (a:=35) (p:=151) (origin:=origin) (removed:=1320869557) (by decide) v35 c36 rfl (by decide) (by decide) rfl

private def ps37 : List ℕ := 157::ps36

private theorem h37_8 : R 8 sa8 3536036129=604747127 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=3536036129) (start:=3536036129) rfl rfl rfl (by decide +kernel)
private theorem h37_16 : R 16 sa16 3536036129=481208470 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=3536036129) (start:=604747127) rfl rfl h37_8 (by decide +kernel)
private theorem h37_24 : R 24 sa24 3536036129=429882255 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=3536036129) (start:=481208470) rfl rfl h37_16 (by decide +kernel)
private theorem h37_32 : R 32 sa32 3536036129=399572149 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=3536036129) (start:=429882255) rfl rfl h37_24 (by decide +kernel)
private theorem c37 : R 36 ps36 3536036129=388562091 :=
  continue_at (portion:=sc36) (base:=sa32) (rank:=36) (baseRank:=32) (t:=3536036129) (start:=399572149) rfl rfl h37_32 (by decide +kernel)
private theorem v37 : R 37 ps37 555157672301=origin-2116129830 :=
  transfer (a:=36) (p:=157) (origin:=origin) (removed:=1727567739) (by decide) v36 c37 rfl (by decide) (by decide) rfl

private def ps38 : List ℕ := 163::ps37

private theorem h38_8 : R 8 sa8 3405875290=582486491 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=3405875290) (start:=3405875290) rfl rfl rfl (by decide +kernel)
private theorem h38_16 : R 16 sa16 3405875290=463495269 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=3405875290) (start:=582486491) rfl rfl h38_8 (by decide +kernel)
private theorem h38_24 : R 24 sa24 3405875290=414058559 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=3405875290) (start:=463495269) rfl rfl h38_16 (by decide +kernel)
private theorem h38_32 : R 32 sa32 3405875290=384863748 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=3405875290) (start:=414058559) rfl rfl h38_24 (by decide +kernel)
private theorem c38 : R 37 ps37 3405875290=371871504 :=
  continue_at (portion:=sc37) (base:=sa32) (rank:=37) (baseRank:=32) (t:=3405875290) (start:=384863748) rfl rfl h38_32 (by decide +kernel)
private theorem v38 : R 38 ps38 555157672301=origin-2488001334 :=
  transfer (a:=37) (p:=163) (origin:=origin) (removed:=2116129830) (by decide) v37 c38 rfl (by decide) (by decide) rfl

private def ps39 : List ℕ := 167::ps38

private theorem h39_8 : R 8 sa8 3324297438=568534719 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=3324297438) (start:=3324297438) rfl rfl rfl (by decide +kernel)
private theorem h39_16 : R 16 sa16 3324297438=452393559 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=3324297438) (start:=568534719) rfl rfl h39_8 (by decide +kernel)
private theorem h39_24 : R 24 sa24 3324297438=404141041 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=3324297438) (start:=452393559) rfl rfl h39_16 (by decide +kernel)
private theorem h39_32 : R 32 sa32 3324297438=375645278 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=3324297438) (start:=404141041) rfl rfl h39_24 (by decide +kernel)
private theorem c39 : R 38 ps38 3324297438=360733399 :=
  continue_at (portion:=sc38) (base:=sa32) (rank:=38) (baseRank:=32) (t:=3324297438) (start:=375645278) rfl rfl h39_32 (by decide +kernel)
private theorem v39 : R 39 ps39 555157672301=origin-2848734733 :=
  transfer (a:=38) (p:=167) (origin:=origin) (removed:=2488001334) (by decide) v38 c39 rfl (by decide) (by decide) rfl

private def ps40 : List ℕ := 173::ps39

private theorem h40_8 : R 8 sa8 3209003886=548816750 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=3209003886) (start:=3209003886) rfl rfl rfl (by decide +kernel)
private theorem h40_16 : R 16 sa16 3209003886=436703598 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=3209003886) (start:=548816750) rfl rfl h40_8 (by decide +kernel)
private theorem h40_24 : R 24 sa24 3209003886=390124785 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=3209003886) (start:=436703598) rfl rfl h40_16 (by decide +kernel)
private theorem h40_32 : R 32 sa32 3209003886=362616952 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=3209003886) (start:=390124785) rfl rfl h40_24 (by decide +kernel)
private theorem c40 : R 39 ps39 3209003886=346132189 :=
  continue_at (portion:=sc39) (base:=sa32) (rank:=39) (baseRank:=32) (t:=3209003886) (start:=362616952) rfl rfl h40_32 (by decide +kernel)
private theorem v40 : R 40 ps40 555157672301=origin-3194866922 :=
  transfer (a:=39) (p:=173) (origin:=origin) (removed:=2848734733) (by decide) v39 c40 rfl (by decide) (by decide) rfl

private def ps41 : List ℕ := 179::ps40

private theorem h41_8 : R 8 sa8 3101439510=530420660 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=3101439510) (start:=3101439510) rfl rfl rfl (by decide +kernel)
private theorem h41_16 : R 16 sa16 3101439510=422065505 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=3101439510) (start:=530420660) rfl rfl h41_8 (by decide +kernel)
private theorem h41_24 : R 24 sa24 3101439510=377048108 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=3101439510) (start:=422065505) rfl rfl h41_16 (by decide +kernel)
private theorem h41_32 : R 32 sa32 3101439510=350461924 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=3101439510) (start:=377048108) rfl rfl h41_24 (by decide +kernel)
private theorem c41 : R 40 ps40 3101439510=332590342 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=3101439510) (start:=350461924) rfl rfl h41_32 (by decide +kernel)
private theorem v41 : R 41 ps41 555157672301=origin-3527457264 :=
  transfer (a:=40) (p:=179) (origin:=origin) (removed:=3194866922) (by decide) v40 c41 rfl (by decide) (by decide) rfl

private def ps42 : List ℕ := 181::ps41

private theorem h42_8 : R 8 sa8 3067169460=524559659 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=3067169460) (start:=3067169460) rfl rfl rfl (by decide +kernel)
private theorem h42_16 : R 16 sa16 3067169460=417401800 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=3067169460) (start:=524559659) rfl rfl h42_8 (by decide +kernel)
private theorem h42_24 : R 24 sa24 3067169460=372881872 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=3067169460) (start:=417401800) rfl rfl h42_16 (by decide +kernel)
private theorem h42_32 : R 32 sa32 3067169460=346589397 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=3067169460) (start:=372881872) rfl rfl h42_24 (by decide +kernel)
private theorem h42_40 : R 40 sa40 3067169460=328914899 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=3067169460) (start:=346589397) rfl rfl h42_32 (by decide +kernel)
private theorem c42 : R 41 ps41 3067169460=327072254 :=
  continue_at (portion:=sc41) (base:=sa40) (rank:=41) (baseRank:=40) (t:=3067169460) (start:=328914899) rfl rfl h42_40 (by decide +kernel)
private theorem v42 : R 42 ps42 555157672301=origin-3854529518 :=
  transfer (a:=41) (p:=181) (origin:=origin) (removed:=3527457264) (by decide) v41 c42 rfl (by decide) (by decide) rfl

private def ps43 : List ℕ := 191::ps42

private theorem h43_8 : R 8 sa8 2906584671=497095804 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2906584671) (start:=2906584671) rfl rfl rfl (by decide +kernel)
private theorem h43_16 : R 16 sa16 2906584671=395548305 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2906584671) (start:=497095804) rfl rfl h43_8 (by decide +kernel)
private theorem h43_24 : R 24 sa24 2906584671=353359462 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2906584671) (start:=395548305) rfl rfl h43_16 (by decide +kernel)
private theorem h43_32 : R 32 sa32 2906584671=328442950 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2906584671) (start:=353359462) rfl rfl h43_24 (by decide +kernel)
private theorem h43_40 : R 40 sa40 2906584671=311692198 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2906584671) (start:=328442950) rfl rfl h43_32 (by decide +kernel)
private theorem c43 : R 42 ps42 2906584671=308227887 :=
  continue_at (portion:=sc42) (base:=sa40) (rank:=42) (baseRank:=40) (t:=2906584671) (start:=311692198) rfl rfl h43_40 (by decide +kernel)
private theorem v43 : R 43 ps43 555157672301=origin-4162757405 :=
  transfer (a:=42) (p:=191) (origin:=origin) (removed:=3854529518) (by decide) v42 c43 rfl (by decide) (by decide) rfl

private def ps44 : List ℕ := 193::ps43

private theorem h44_8 : R 8 sa8 2876464623=491944553 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2876464623) (start:=2876464623) rfl rfl rfl (by decide +kernel)
private theorem h44_16 : R 16 sa16 2876464623=391449368 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2876464623) (start:=491944553) rfl rfl h44_8 (by decide +kernel)
private theorem h44_24 : R 24 sa24 2876464623=349697768 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2876464623) (start:=391449368) rfl rfl h44_16 (by decide +kernel)
private theorem h44_32 : R 32 sa32 2876464623=325039410 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2876464623) (start:=349697768) rfl rfl h44_24 (by decide +kernel)
private theorem h44_40 : R 40 sa40 2876464623=308461908 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2876464623) (start:=325039410) rfl rfl h44_32 (by decide +kernel)
private theorem c44 : R 43 ps43 2876464623=303430524 :=
  continue_at (portion:=sc43) (base:=sa40) (rank:=43) (baseRank:=40) (t:=2876464623) (start:=308461908) rfl rfl h44_40 (by decide +kernel)
private theorem v44 : R 44 ps44 555157672301=origin-4466187929 :=
  transfer (a:=43) (p:=193) (origin:=origin) (removed:=4162757405) (by decide) v43 c44 rfl (by decide) (by decide) rfl

private def ps45 : List ℕ := 197::ps44

private theorem h45_8 : R 8 sa8 2818059250=481955831 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2818059250) (start:=2818059250) rfl rfl rfl (by decide +kernel)
private theorem h45_16 : R 16 sa16 2818059250=383501165 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2818059250) (start:=481955831) rfl rfl h45_8 (by decide +kernel)
private theorem h45_24 : R 24 sa24 2818059250=342597368 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2818059250) (start:=383501165) rfl rfl h45_16 (by decide +kernel)
private theorem h45_32 : R 32 sa32 2818059250=318439408 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2818059250) (start:=342597368) rfl rfl h45_24 (by decide +kernel)
private theorem h45_40 : R 40 sa40 2818059250=302197818 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2818059250) (start:=318439408) rfl rfl h45_32 (by decide +kernel)
private theorem c45 : R 44 ps44 2818059250=295722042 :=
  continue_at (portion:=sc44) (base:=sa40) (rank:=44) (baseRank:=40) (t:=2818059250) (start:=302197818) rfl rfl h45_40 (by decide +kernel)
private theorem v45 : R 45 ps45 555157672301=origin-4761909971 :=
  transfer (a:=44) (p:=197) (origin:=origin) (removed:=4466187929) (by decide) v44 c45 rfl (by decide) (by decide) rfl

private def ps46 : List ℕ := 199::ps45

private theorem h46_8 : R 8 sa8 2789737046=477112048 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2789737046) (start:=2789737046) rfl rfl rfl (by decide +kernel)
private theorem h46_16 : R 16 sa16 2789737046=379646876 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2789737046) (start:=477112048) rfl rfl h46_8 (by decide +kernel)
private theorem h46_24 : R 24 sa24 2789737046=339154201 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2789737046) (start:=379646876) rfl rfl h46_16 (by decide +kernel)
private theorem h46_32 : R 32 sa32 2789737046=315238895 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2789737046) (start:=339154201) rfl rfl h46_24 (by decide +kernel)
private theorem h46_40 : R 40 sa40 2789737046=299160208 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2789737046) (start:=315238895) rfl rfl h46_32 (by decide +kernel)
private theorem c46 : R 45 ps45 2789737046=291256926 :=
  continue_at (portion:=sc45) (base:=sa40) (rank:=45) (baseRank:=40) (t:=2789737046) (start:=299160208) rfl rfl h46_40 (by decide +kernel)
private theorem v46 : R 46 ps46 555157672301=origin-5053166897 :=
  transfer (a:=45) (p:=199) (origin:=origin) (removed:=4761909971) (by decide) v45 c46 rfl (by decide) (by decide) rfl

private def ps47 : List ℕ := 211::ps46

private theorem h47_8 : R 8 sa8 2631079015=449977715 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2631079015) (start:=2631079015) rfl rfl rfl (by decide +kernel)
private theorem h47_16 : R 16 sa16 2631079015=358055556 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2631079015) (start:=449977715) rfl rfl h47_8 (by decide +kernel)
private theorem h47_24 : R 24 sa24 2631079015=319866069 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2631079015) (start:=358055556) rfl rfl h47_16 (by decide +kernel)
private theorem h47_32 : R 32 sa32 2631079015=297310178 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2631079015) (start:=319866069) rfl rfl h47_24 (by decide +kernel)
private theorem h47_40 : R 40 sa40 2631079015=282144289 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2631079015) (start:=297310178) rfl rfl h47_32 (by decide +kernel)
private theorem c47 : R 46 ps46 2631079015=273302578 :=
  continue_at (portion:=sc46) (base:=sa40) (rank:=46) (baseRank:=40) (t:=2631079015) (start:=282144289) rfl rfl h47_40 (by decide +kernel)
private theorem v47 : R 47 ps47 555157672301=origin-5326469475 :=
  transfer (a:=46) (p:=211) (origin:=origin) (removed:=5053166897) (by decide) v46 c47 rfl (by decide) (by decide) rfl

private def ps48 : List ℕ := 223::ps47

private theorem h48_8 : R 8 sa8 2489496288=425763670 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2489496288) (start:=2489496288) rfl rfl rfl (by decide +kernel)
private theorem h48_16 : R 16 sa16 2489496288=338788014 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2489496288) (start:=425763670) rfl rfl h48_8 (by decide +kernel)
private theorem h48_24 : R 24 sa24 2489496288=302653650 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2489496288) (start:=338788014) rfl rfl h48_16 (by decide +kernel)
private theorem h48_32 : R 32 sa32 2489496288=281310897 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2489496288) (start:=302653650) rfl rfl h48_24 (by decide +kernel)
private theorem h48_40 : R 40 sa40 2489496288=266959606 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2489496288) (start:=281310897) rfl rfl h48_32 (by decide +kernel)
private theorem c48 : R 47 ps47 2489496288=257360792 :=
  continue_at (portion:=sc47) (base:=sa40) (rank:=47) (baseRank:=40) (t:=2489496288) (start:=266959606) rfl rfl h48_40 (by decide +kernel)
private theorem v48 : R 48 ps48 555157672301=origin-5583830267 :=
  transfer (a:=47) (p:=223) (origin:=origin) (removed:=5326469475) (by decide) v47 c48 rfl (by decide) (by decide) rfl

private def ps49 : List ℕ := 227::ps48

private theorem h49_8 : R 8 sa8 2445628512=418261227 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2445628512) (start:=2445628512) rfl rfl rfl (by decide +kernel)
private theorem h49_16 : R 16 sa16 2445628512=332818181 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2445628512) (start:=418261227) rfl rfl h49_8 (by decide +kernel)
private theorem h49_24 : R 24 sa24 2445628512=297320646 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2445628512) (start:=332818181) rfl rfl h49_16 (by decide +kernel)
private theorem h49_32 : R 32 sa32 2445628512=276353770 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2445628512) (start:=297320646) rfl rfl h49_24 (by decide +kernel)
private theorem h49_40 : R 40 sa40 2445628512=262254747 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2445628512) (start:=276353770) rfl rfl h49_32 (by decide +kernel)
private theorem c49 : R 48 ps48 2445628512=251684914 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=2445628512) (start:=262254747) rfl rfl h49_40 (by decide +kernel)
private theorem v49 : R 49 ps49 555157672301=origin-5835515181 :=
  transfer (a:=48) (p:=227) (origin:=origin) (removed:=5583830267) (by decide) v48 c49 rfl (by decide) (by decide) rfl

private def ps50 : List ℕ := 229::ps49

private theorem h50_8 : R 8 sa8 2424269311=414608290 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2424269311) (start:=2424269311) rfl rfl rfl (by decide +kernel)
private theorem h50_16 : R 16 sa16 2424269311=329911471 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2424269311) (start:=414608290) rfl rfl h50_8 (by decide +kernel)
private theorem h50_24 : R 24 sa24 2424269311=294723986 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2424269311) (start:=329911471) rfl rfl h50_16 (by decide +kernel)
private theorem h50_32 : R 32 sa32 2424269311=273940078 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2424269311) (start:=294723986) rfl rfl h50_24 (by decide +kernel)
private theorem h50_40 : R 40 sa40 2424269311=259963972 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2424269311) (start:=273940078) rfl rfl h50_32 (by decide +kernel)
private theorem h50_48 : R 48 sa48 2424269311=249486281 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=2424269311) (start:=259963972) rfl rfl h50_40 (by decide +kernel)
private theorem c50 : R 49 ps49 2424269311=248381166 :=
  continue_at (portion:=sc49) (base:=sa48) (rank:=49) (baseRank:=48) (t:=2424269311) (start:=249486281) rfl rfl h50_48 (by decide +kernel)
private theorem v50 : R 50 ps50 555157672301=origin-6083896347 :=
  transfer (a:=49) (p:=229) (origin:=origin) (removed:=5835515181) (by decide) v49 c50 rfl (by decide) (by decide) rfl

private def ps51 : List ℕ := 233::ps50

private theorem h51_8 : R 8 sa8 2382650954=407490548 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2382650954) (start:=2382650954) rfl rfl rfl (by decide +kernel)
private theorem h51_16 : R 16 sa16 2382650954=324247753 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2382650954) (start:=407490548) rfl rfl h51_8 (by decide +kernel)
private theorem h51_24 : R 24 sa24 2382650954=289664392 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2382650954) (start:=324247753) rfl rfl h51_16 (by decide +kernel)
private theorem h51_32 : R 32 sa32 2382650954=269237111 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2382650954) (start:=289664392) rfl rfl h51_24 (by decide +kernel)
private theorem h51_40 : R 40 sa40 2382650954=255500543 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2382650954) (start:=269237111) rfl rfl h51_32 (by decide +kernel)
private theorem h51_48 : R 48 sa48 2382650954=245202317 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=2382650954) (start:=255500543) rfl rfl h51_40 (by decide +kernel)
private theorem c51 : R 50 ps50 2382650954=243044223 :=
  continue_at (portion:=sc50) (base:=sa48) (rank:=50) (baseRank:=48) (t:=2382650954) (start:=245202317) rfl rfl h51_48 (by decide +kernel)
private theorem v51 : R 51 ps51 555157672301=origin-6326940570 :=
  transfer (a:=50) (p:=233) (origin:=origin) (removed:=6083896347) (by decide) v50 c51 rfl (by decide) (by decide) rfl

private def ps52 : List ℕ := 239::ps51

private theorem h52_8 : R 8 sa8 2322835448=397260665 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2322835448) (start:=2322835448) rfl rfl rfl (by decide +kernel)
private theorem h52_16 : R 16 sa16 2322835448=316107641 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2322835448) (start:=397260665) rfl rfl h52_8 (by decide +kernel)
private theorem h52_24 : R 24 sa24 2322835448=282392573 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2322835448) (start:=316107641) rfl rfl h52_16 (by decide +kernel)
private theorem h52_32 : R 32 sa32 2322835448=262477772 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2322835448) (start:=282392573) rfl rfl h52_24 (by decide +kernel)
private theorem h52_40 : R 40 sa40 2322835448=249085360 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2322835448) (start:=262477772) rfl rfl h52_32 (by decide +kernel)
private theorem h52_48 : R 48 sa48 2322835448=239045138 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=2322835448) (start:=249085360) rfl rfl h52_40 (by decide +kernel)
private theorem c52 : R 51 ps51 2322835448=235918617 :=
  continue_at (portion:=sc51) (base:=sa48) (rank:=51) (baseRank:=48) (t:=2322835448) (start:=239045138) rfl rfl h52_48 (by decide +kernel)
private theorem v52 : R 52 ps52 555157672301=origin-6562859187 :=
  transfer (a:=51) (p:=239) (origin:=origin) (removed:=6326940570) (by decide) v51 c52 rfl (by decide) (by decide) rfl

private def ps53 : List ℕ := 241::ps52

private theorem h53_8 : R 8 sa8 2303558806=393963891 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2303558806) (start:=2303558806) rfl rfl rfl (by decide +kernel)
private theorem h53_16 : R 16 sa16 2303558806=313484359 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2303558806) (start:=393963891) rfl rfl h53_8 (by decide +kernel)
private theorem h53_24 : R 24 sa24 2303558806=280049116 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2303558806) (start:=313484359) rfl rfl h53_16 (by decide +kernel)
private theorem h53_32 : R 32 sa32 2303558806=260299450 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2303558806) (start:=280049116) rfl rfl h53_24 (by decide +kernel)
private theorem h53_40 : R 40 sa40 2303558806=247017996 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2303558806) (start:=260299450) rfl rfl h53_32 (by decide +kernel)
private theorem h53_48 : R 48 sa48 2303558806=237060985 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=2303558806) (start:=247017996) rfl rfl h53_40 (by decide +kernel)
private theorem c53 : R 52 ps52 2303558806=232976076 :=
  continue_at (portion:=sc52) (base:=sa48) (rank:=52) (baseRank:=48) (t:=2303558806) (start:=237060985) rfl rfl h53_48 (by decide +kernel)
private theorem v53 : R 53 ps53 555157672301=origin-6795835263 :=
  transfer (a:=52) (p:=241) (origin:=origin) (removed:=6562859187) (by decide) v52 c53 rfl (by decide) (by decide) rfl

private def ps54 : List ℕ := 251::ps53

private theorem h54_8 : R 8 sa8 2211783554=378268116 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2211783554) (start:=2211783554) rfl rfl rfl (by decide +kernel)
private theorem h54_16 : R 16 sa16 2211783554=300994934 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2211783554) (start:=378268116) rfl rfl h54_8 (by decide +kernel)
private theorem h54_24 : R 24 sa24 2211783554=268891860 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2211783554) (start:=300994934) rfl rfl h54_16 (by decide +kernel)
private theorem h54_32 : R 32 sa32 2211783554=249928575 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2211783554) (start:=268891860) rfl rfl h54_24 (by decide +kernel)
private theorem h54_40 : R 40 sa40 2211783554=237175088 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2211783554) (start:=249928575) rfl rfl h54_32 (by decide +kernel)
private theorem h54_48 : R 48 sa48 2211783554=227614141 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=2211783554) (start:=237175088) rfl rfl h54_40 (by decide +kernel)
private theorem c54 : R 53 ps53 2211783554=222758732 :=
  continue_at (portion:=sc53) (base:=sa48) (rank:=53) (baseRank:=48) (t:=2211783554) (start:=227614141) rfl rfl h54_48 (by decide +kernel)
private theorem v54 : R 54 ps54 555157672301=origin-7018593995 :=
  transfer (a:=53) (p:=251) (origin:=origin) (removed:=6795835263) (by decide) v53 c54 rfl (by decide) (by decide) rfl

private def ps55 : List ℕ := 257::ps54

private theorem h55_8 : R 8 sa8 2160146584=369436957 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2160146584) (start:=2160146584) rfl rfl rfl (by decide +kernel)
private theorem h55_16 : R 16 sa16 2160146584=293967806 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2160146584) (start:=369436957) rfl rfl h55_8 (by decide +kernel)
private theorem h55_24 : R 24 sa24 2160146584=262614266 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2160146584) (start:=293967806) rfl rfl h55_16 (by decide +kernel)
private theorem h55_32 : R 32 sa32 2160146584=244093351 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2160146584) (start:=262614266) rfl rfl h55_24 (by decide +kernel)
private theorem h55_40 : R 40 sa40 2160146584=231637022 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2160146584) (start:=244093351) rfl rfl h55_32 (by decide +kernel)
private theorem h55_48 : R 48 sa48 2160146584=222298854 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=2160146584) (start:=231637022) rfl rfl h55_40 (by decide +kernel)
private theorem c55 : R 54 ps54 2160146584=216685714 :=
  continue_at (portion:=sc54) (base:=sa48) (rank:=54) (baseRank:=48) (t:=2160146584) (start:=222298854) rfl rfl h55_48 (by decide +kernel)
private theorem v55 : R 55 ps55 555157672301=origin-7235279709 :=
  transfer (a:=54) (p:=257) (origin:=origin) (removed:=7018593995) (by decide) v54 c55 rfl (by decide) (by decide) rfl

private def ps56 : List ℕ := 263::ps55

private theorem h56_8 : R 8 sa8 2110865674=361008738 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2110865674) (start:=2110865674) rfl rfl rfl (by decide +kernel)
private theorem h56_16 : R 16 sa16 2110865674=287261312 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2110865674) (start:=361008738) rfl rfl h56_8 (by decide +kernel)
private theorem h56_24 : R 24 sa24 2110865674=256623162 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2110865674) (start:=287261312) rfl rfl h56_16 (by decide +kernel)
private theorem h56_32 : R 32 sa32 2110865674=238524523 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2110865674) (start:=256623162) rfl rfl h56_24 (by decide +kernel)
private theorem h56_40 : R 40 sa40 2110865674=226351837 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2110865674) (start:=238524523) rfl rfl h56_32 (by decide +kernel)
private theorem h56_48 : R 48 sa48 2110865674=217226383 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=2110865674) (start:=226351837) rfl rfl h56_40 (by decide +kernel)
private theorem c56 : R 55 ps55 2110865674=210913599 :=
  continue_at (portion:=sc55) (base:=sa48) (rank:=55) (baseRank:=48) (t:=2110865674) (start:=217226383) rfl rfl h56_48 (by decide +kernel)
private theorem v56 : R 56 ps56 555157672301=origin-7446193308 :=
  transfer (a:=55) (p:=263) (origin:=origin) (removed:=7235279709) (by decide) v55 c56 rfl (by decide) (by decide) rfl

private def ps57 : List ℕ := 269::ps56

private theorem h57_8 : R 8 sa8 2063783168=352956497 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2063783168) (start:=2063783168) rfl rfl rfl (by decide +kernel)
private theorem h57_16 : R 16 sa16 2063783168=280854022 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2063783168) (start:=352956497) rfl rfl h57_8 (by decide +kernel)
private theorem h57_24 : R 24 sa24 2063783168=250899346 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2063783168) (start:=280854022) rfl rfl h57_16 (by decide +kernel)
private theorem h57_32 : R 32 sa32 2063783168=233204080 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2063783168) (start:=250899346) rfl rfl h57_24 (by decide +kernel)
private theorem h57_40 : R 40 sa40 2063783168=221302243 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2063783168) (start:=233204080) rfl rfl h57_32 (by decide +kernel)
private theorem h57_48 : R 48 sa48 2063783168=212380029 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=2063783168) (start:=221302243) rfl rfl h57_40 (by decide +kernel)
private theorem c57 : R 56 ps56 2063783168=205420741 :=
  continue_at (portion:=sc56) (base:=sa48) (rank:=56) (baseRank:=48) (t:=2063783168) (start:=212380029) rfl rfl h57_48 (by decide +kernel)
private theorem v57 : R 57 ps57 555157672301=origin-7651614049 :=
  transfer (a:=56) (p:=269) (origin:=origin) (removed:=7446193308) (by decide) v56 c57 rfl (by decide) (by decide) rfl

private def ps58 : List ℕ := 271::ps57

private theorem h58_8 : R 8 sa8 2048552296=350351657 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2048552296) (start:=2048552296) rfl rfl rfl (by decide +kernel)
private theorem h58_16 : R 16 sa16 2048552296=278781272 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2048552296) (start:=350351657) rfl rfl h58_8 (by decide +kernel)
private theorem h58_24 : R 24 sa24 2048552296=249047627 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2048552296) (start:=278781272) rfl rfl h58_16 (by decide +kernel)
private theorem h58_32 : R 32 sa32 2048552296=231482858 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2048552296) (start:=249047627) rfl rfl h58_24 (by decide +kernel)
private theorem h58_40 : R 40 sa40 2048552296=219668698 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2048552296) (start:=231482858) rfl rfl h58_32 (by decide +kernel)
private theorem h58_48 : R 48 sa48 2048552296=210812253 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=2048552296) (start:=219668698) rfl rfl h58_40 (by decide +kernel)
private theorem h58_56 : R 56 sa56 2048552296=203904449 :=
  continue_at (portion:=sc56) (base:=sa48) (rank:=56) (baseRank:=48) (t:=2048552296) (start:=210812253) rfl rfl h58_48 (by decide +kernel)
private theorem c58 : R 57 ps57 2048552296=203143265 :=
  continue_at (portion:=sc57) (base:=sa56) (rank:=57) (baseRank:=56) (t:=2048552296) (start:=203904449) rfl rfl h58_56 (by decide +kernel)
private theorem v58 : R 58 ps58 555157672301=origin-7854757314 :=
  transfer (a:=57) (p:=271) (origin:=origin) (removed:=7651614049) (by decide) v57 c58 rfl (by decide) (by decide) rfl

private def ps59 : List ℕ := 277::ps58

private theorem h59_8 : R 8 sa8 2004179322=342762810 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=2004179322) (start:=2004179322) rfl rfl rfl (by decide +kernel)
private theorem h59_16 : R 16 sa16 2004179322=272742684 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=2004179322) (start:=342762810) rfl rfl h59_8 (by decide +kernel)
private theorem h59_24 : R 24 sa24 2004179322=243653162 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=2004179322) (start:=272742684) rfl rfl h59_16 (by decide +kernel)
private theorem h59_32 : R 32 sa32 2004179322=226468599 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=2004179322) (start:=243653162) rfl rfl h59_24 (by decide +kernel)
private theorem h59_40 : R 40 sa40 2004179322=214909734 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=2004179322) (start:=226468599) rfl rfl h59_32 (by decide +kernel)
private theorem h59_48 : R 48 sa48 2004179322=206244830 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=2004179322) (start:=214909734) rfl rfl h59_40 (by decide +kernel)
private theorem h59_56 : R 56 sa56 2004179322=199486994 :=
  continue_at (portion:=sc56) (base:=sa48) (rank:=56) (baseRank:=48) (t:=2004179322) (start:=206244830) rfl rfl h59_48 (by decide +kernel)
private theorem c59 : R 58 ps58 2004179322=198006237 :=
  continue_at (portion:=sc58) (base:=sa56) (rank:=58) (baseRank:=56) (t:=2004179322) (start:=199486994) rfl rfl h59_56 (by decide +kernel)
private theorem v59 : R 59 ps59 555157672301=origin-8052763551 :=
  transfer (a:=58) (p:=277) (origin:=origin) (removed:=7854757314) (by decide) v58 c59 rfl (by decide) (by decide) rfl

private def ps60 : List ℕ := 281::ps59

private theorem h60_8 : R 8 sa8 1975650079=337883624 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=1975650079) (start:=1975650079) rfl rfl rfl (by decide +kernel)
private theorem h60_16 : R 16 sa16 1975650079=268860244 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=1975650079) (start:=337883624) rfl rfl h60_8 (by decide +kernel)
private theorem h60_24 : R 24 sa24 1975650079=240184847 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=1975650079) (start:=268860244) rfl rfl h60_16 (by decide +kernel)
private theorem h60_32 : R 32 sa32 1975650079=223244674 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=1975650079) (start:=240184847) rfl rfl h60_24 (by decide +kernel)
private theorem h60_40 : R 40 sa40 1975650079=211850045 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=1975650079) (start:=223244674) rfl rfl h60_32 (by decide +kernel)
private theorem h60_48 : R 48 sa48 1975650079=203308374 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=1975650079) (start:=211850045) rfl rfl h60_40 (by decide +kernel)
private theorem h60_56 : R 56 sa56 1975650079=196646996 :=
  continue_at (portion:=sc56) (base:=sa48) (rank:=56) (baseRank:=48) (t:=1975650079) (start:=203308374) rfl rfl h60_48 (by decide +kernel)
private theorem c60 : R 59 ps59 1975650079=194480428 :=
  continue_at (portion:=sc59) (base:=sa56) (rank:=59) (baseRank:=56) (t:=1975650079) (start:=196646996) rfl rfl h60_56 (by decide +kernel)
private theorem v60 : R 60 ps60 555157672301=origin-8247243979 :=
  transfer (a:=59) (p:=281) (origin:=origin) (removed:=8052763551) (by decide) v59 c60 rfl (by decide) (by decide) rfl

private def ps61 : List ℕ := 283::ps60

private theorem h61_8 : R 8 sa8 1961687887=335495752 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=1961687887) (start:=1961687887) rfl rfl rfl (by decide +kernel)
private theorem h61_16 : R 16 sa16 1961687887=266960163 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=1961687887) (start:=335495752) rfl rfl h61_8 (by decide +kernel)
private theorem h61_24 : R 24 sa24 1961687887=238487431 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=1961687887) (start:=266960163) rfl rfl h61_16 (by decide +kernel)
private theorem h61_32 : R 32 sa32 1961687887=221666909 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=1961687887) (start:=238487431) rfl rfl h61_24 (by decide +kernel)
private theorem h61_40 : R 40 sa40 1961687887=210352625 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=1961687887) (start:=221666909) rfl rfl h61_32 (by decide +kernel)
private theorem h61_48 : R 48 sa48 1961687887=201871169 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=1961687887) (start:=210352625) rfl rfl h61_40 (by decide +kernel)
private theorem h61_56 : R 56 sa56 1961687887=195256975 :=
  continue_at (portion:=sc56) (base:=sa48) (rank:=56) (baseRank:=48) (t:=1961687887) (start:=201871169) rfl rfl h61_48 (by decide +kernel)
private theorem c61 : R 60 ps60 1961687887=192416643 :=
  continue_at (portion:=sc60) (base:=sa56) (rank:=60) (baseRank:=56) (t:=1961687887) (start:=195256975) rfl rfl h61_56 (by decide +kernel)
private theorem v61 : R 61 ps61 555157672301=origin-8439660622 :=
  transfer (a:=60) (p:=283) (origin:=origin) (removed:=8247243979) (by decide) v60 c61 rfl (by decide) (by decide) rfl

private def ps62 : List ℕ := 293::ps61

private theorem h62_8 : R 8 sa8 1894736082=324045384 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=1894736082) (start:=1894736082) rfl rfl rfl (by decide +kernel)
private theorem h62_16 : R 16 sa16 1894736082=257848902 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=1894736082) (start:=324045384) rfl rfl h62_8 (by decide +kernel)
private theorem h62_24 : R 24 sa24 1894736082=230348005 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=1894736082) (start:=257848902) rfl rfl h62_16 (by decide +kernel)
private theorem h62_32 : R 32 sa32 1894736082=214101125 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=1894736082) (start:=230348005) rfl rfl h62_24 (by decide +kernel)
private theorem h62_40 : R 40 sa40 1894736082=203172146 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=1894736082) (start:=214101125) rfl rfl h62_32 (by decide +kernel)
private theorem h62_48 : R 48 sa48 1894736082=194979777 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=1894736082) (start:=203172146) rfl rfl h62_40 (by decide +kernel)
private theorem h62_56 : R 56 sa56 1894736082=188591915 :=
  continue_at (portion:=sc56) (base:=sa48) (rank:=56) (baseRank:=48) (t:=1894736082) (start:=194979777) rfl rfl h62_48 (by decide +kernel)
private theorem c62 : R 61 ps61 1894736082=185191098 :=
  continue_at (portion:=sc61) (base:=sa56) (rank:=61) (baseRank:=56) (t:=1894736082) (start:=188591915) rfl rfl h62_56 (by decide +kernel)
private theorem v62 : R 62 ps62 555157672301=origin-8624851720 :=
  transfer (a:=61) (p:=293) (origin:=origin) (removed:=8439660622) (by decide) v61 c62 rfl (by decide) (by decide) rfl

private def ps63 : List ℕ := 307::ps62

private theorem h63_8 : R 8 sa8 1808331180=309268069 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=1808331180) (start:=1808331180) rfl rfl rfl (by decide +kernel)
private theorem h63_16 : R 16 sa16 1808331180=246090339 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=1808331180) (start:=309268069) rfl rfl h63_8 (by decide +kernel)
private theorem h63_24 : R 24 sa24 1808331180=219843629 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=1808331180) (start:=246090339) rfl rfl h63_16 (by decide +kernel)
private theorem h63_32 : R 32 sa32 1808331180=204337027 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=1808331180) (start:=219843629) rfl rfl h63_24 (by decide +kernel)
private theorem h63_40 : R 40 sa40 1808331180=193905363 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=1808331180) (start:=204337027) rfl rfl h63_32 (by decide +kernel)
private theorem h63_48 : R 48 sa48 1808331180=186086197 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=1808331180) (start:=193905363) rfl rfl h63_40 (by decide +kernel)
private theorem h63_56 : R 56 sa56 1808331180=179990398 :=
  continue_at (portion:=sc56) (base:=sa48) (rank:=56) (baseRank:=48) (t:=1808331180) (start:=186086197) rfl rfl h63_48 (by decide +kernel)
private theorem c63 : R 62 ps62 1808331180=176141865 :=
  continue_at (portion:=sc62) (base:=sa56) (rank:=62) (baseRank:=56) (t:=1808331180) (start:=179990398) rfl rfl h63_56 (by decide +kernel)
private theorem v63 : R 63 ps63 555157672301=origin-8800993585 :=
  transfer (a:=62) (p:=307) (origin:=origin) (removed:=8624851720) (by decide) v62 c63 rfl (by decide) (by decide) rfl

private def ps64 : List ℕ := 311::ps63

private theorem h64_8 : R 8 sa8 1785072901=305290351 :=
  continue_at (portion:=sc8) (base:=sa0) (rank:=8) (baseRank:=0) (t:=1785072901) (start:=1785072901) rfl rfl rfl (by decide +kernel)
private theorem h64_16 : R 16 sa16 1785072901=242925203 :=
  continue_at (portion:=sc16) (base:=sa8) (rank:=16) (baseRank:=8) (t:=1785072901) (start:=305290351) rfl rfl h64_8 (by decide +kernel)
private theorem h64_24 : R 24 sa24 1785072901=217016109 :=
  continue_at (portion:=sc24) (base:=sa16) (rank:=24) (baseRank:=16) (t:=1785072901) (start:=242925203) rfl rfl h64_16 (by decide +kernel)
private theorem h64_32 : R 32 sa32 1785072901=201708813 :=
  continue_at (portion:=sc32) (base:=sa24) (rank:=32) (baseRank:=24) (t:=1785072901) (start:=217016109) rfl rfl h64_24 (by decide +kernel)
private theorem h64_40 : R 40 sa40 1785072901=191411065 :=
  continue_at (portion:=sc40) (base:=sa32) (rank:=40) (baseRank:=32) (t:=1785072901) (start:=201708813) rfl rfl h64_32 (by decide +kernel)
private theorem h64_48 : R 48 sa48 1785072901=183692313 :=
  continue_at (portion:=sc48) (base:=sa40) (rank:=48) (baseRank:=40) (t:=1785072901) (start:=191411065) rfl rfl h64_40 (by decide +kernel)
private theorem h64_56 : R 56 sa56 1785072901=177675158 :=
  continue_at (portion:=sc56) (base:=sa48) (rank:=56) (baseRank:=48) (t:=1785072901) (start:=183692313) rfl rfl h64_48 (by decide +kernel)
private theorem c64 : R 63 ps63 1785072901=173309894 :=
  continue_at (portion:=sc63) (base:=sa56) (rank:=63) (baseRank:=56) (t:=1785072901) (start:=177675158) rfl rfl h64_56 (by decide +kernel)
private theorem v64 : R 64 ps64 555157672301=origin-8974303479 :=
  transfer (a:=63) (p:=311) (origin:=origin) (removed:=8800993585) (by decide) v63 c64 rfl (by decide) (by decide) rfl

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



private def r0_66 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]
private theorem r0_66ok : (List.range' 0 66).filter prime = r0_66 :=
  by decide +kernel

private def r66_132 : List ℕ := [67,71,73,79,83,89,97,101,103,107,109,113,127,131]
private theorem r66_132ok : (List.range' 66 66).filter prime = r66_132 :=
  by decide +kernel

private def r0_132 : List ℕ := r0_66 ++ r66_132
private theorem r0_132ok : (List.range' 0 132).filter prime = r0_132 :=
  merge_filter _ 0 66 66 _ _ r0_66ok r66_132ok

set_option maxRecDepth 20000 in
private theorem row32 :
    ((List.range (131+1)).filter (fun p => decide p.Prime)).reverse = ps32 := by
  rw [filter_from_test prime prime_ok 131 (by decide),List.range_eq_range',r0_132ok]
  rfl

private def r0_78 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73]
private theorem r0_78ok : (List.range' 0 78).filter prime = r0_78 :=
  by decide +kernel

private def r78_156 : List ℕ := [79,83,89,97,101,103,107,109,113,127,131,137,139,149,151]
private theorem r78_156ok : (List.range' 78 78).filter prime = r78_156 :=
  by decide +kernel

private def r0_156 : List ℕ := r0_78 ++ r78_156
private theorem r0_156ok : (List.range' 0 156).filter prime = r0_156 :=
  merge_filter _ 0 78 78 _ _ r0_78ok r78_156ok

private def r156_234 : List ℕ := [157,163,167,173,179,181,191,193,197,199,211,223,227,229,233]
private theorem r156_234ok : (List.range' 156 78).filter prime = r156_234 :=
  by decide +kernel

private def r234_312 : List ℕ := [239,241,251,257,263,269,271,277,281,283,293,307,311]
private theorem r234_312ok : (List.range' 234 78).filter prime = r234_312 :=
  by decide +kernel

private def r156_312 : List ℕ := r156_234 ++ r234_312
private theorem r156_312ok : (List.range' 156 156).filter prime = r156_312 :=
  merge_filter _ 156 78 78 _ _ r156_234ok r234_312ok

private def r0_312 : List ℕ := r0_156 ++ r156_312
private theorem r0_312ok : (List.range' 0 312).filter prime = r0_312 :=
  merge_filter _ 0 156 156 _ _ r0_156ok r156_312ok

set_option maxRecDepth 20000 in
private theorem row64 :
    ((List.range (311+1)).filter (fun p => decide p.Prime)).reverse = ps64 := by
  rw [filter_from_test prime prime_ok 311 (by decide),List.range_eq_range',r0_312ok]
  rfl

private theorem bridge {k a : ℕ} {ps : List ℕ} (kb : k≤100000) (row :
    ((List.range (k+1)).filter (fun p => decide p.Prime)).reverse = ps) (val : tab k=a) :
    ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE k, ¬ p ∣ n)).card = R a ps 555157672301 := by
  have grade : Nat.primeCounting k=a := (FastDenseA100.fast_correct k kb).symm.trans val
  calc
    _ = (((List.range (k+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id) 555157672301 :=
      (legendre_range k 555157672301).symm
    _ = evalPhi tab ((List.range (k+1)).filter (fun p => decide p.Prime)).reverse 555157672301 :=
      agree_range tab FastDenseA100.fast_correct k (by decide) 555157672301
    _ = R (Nat.primeCounting k) ((List.range (k+1)).filter (fun p => decide p.Prime)).reverse 555157672301 :=
      ranked_range tab FastDenseA100.fast_correct k kb 555157672301
    _ = _ := by rw [grade,row]

set_option maxRecDepth 18000 in
theorem exact_change : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 311, ¬ p ∣ n)).card = ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 131, ¬ p ∣ n)).card - 8974303479 := by
  have l : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 131, ¬ p ∣ n)).card=R 32 ps32 555157672301 := bridge (by decide) row32 (by decide +kernel)
  have r : ((Icc 1 555157672301).filter (fun n => ∀ p ∈ Nat.primesLE 311, ¬ p ∣ n)).card=R 64 ps64 555157672301 := bridge (by decide) row64 (by decide +kernel)
  exact r.trans ((v64).trans (congrArg (fun n : ℕ => n-8974303479) l.symm))

end IndexedSlicedSieveA26From32To64
