import FormalConjectures.OEIS.«247824»

/-!
# Sieve counts at 30,110,134,441,897 between prime cutoffs 0 and 53

For integers from 1 through 30,110,134,441,897, this certificate counts the additional
values removed when the prime cutoff rises from 0 to 53.
The Legendre recurrence uses a wheel of period 30,030 and prime counts
through 25,123. The identities adapt Physbuzz's A247824 reduction and
the Palomar proof of Daniel Veljjanoski and rleshner (Apache-2.0).
-/

namespace Sieve30110134441897From0To53

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

end Sieve30110134441897From0To53

open Sieve30110134441897From0To53
open Finset
namespace SieveA30From0To16

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
      if t < (p+1)^2 ∧ t ≤ 25123 then 1 + table t - table p else
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
    (pos : 0 < p) (cap : 25123 ≤ bound) : ∀ t,
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
  · by_cases short : t < (p+1)^2 ∧ t ≤ 25123
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
    (y : ℕ) (cap : 25123 ≤ bound) :
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



private abbrev tab := FastDenseControl.fast
private abbrev F := evalPhi tab
private abbrev prime := FastDenseControl.prime
private theorem prime_ok (n : ℕ) (h : n≤25123) : prime n=true ↔ n.Prime := FastDenseControl.prime_ok n h

private theorem transfer {ps : List ℕ} {p q origin removed step total : ℕ}
    (ne : p≠13) (base : F ps 30110134441897=origin-removed) (part : F ps q=step)
    (div : 30110134441897/p=q) (le : p≤30110134441897) (sq : (p+1)^2≤30110134441897) (sum : removed+step=total) :
    F (p::ps) 30110134441897=origin-total := by
  have eq := eval_delta tab ps p 30110134441897 q (origin-removed) step ((origin-removed)-step)
    ne le sq div base part rfl
  exact eq.trans (by rw [Nat.sub_sub,sum])

private def ps0 : List ℕ := []
private def origin : ℕ := F ps0 30110134441897
private theorem v0 : F ps0 30110134441897=origin-0 := by rw [Nat.sub_zero]; rfl

private def ps1 : List ℕ := 2::ps0

private theorem c1 : F ps0 15055067220948=15055067220948 := by decide +kernel
private theorem v1 : F ps1 30110134441897=origin-15055067220948 :=
  transfer (p:=2) (origin:=origin) (removed:=0) (by decide) v0 c1 rfl (by decide) (by decide) rfl

private def ps2 : List ℕ := 3::ps1

private theorem c2 : F ps1 10036711480632=5018355740316 := by decide +kernel
private theorem v2 : F ps2 30110134441897=origin-20073422961264 :=
  transfer (p:=3) (origin:=origin) (removed:=15055067220948) (by decide) v1 c2 rfl (by decide) (by decide) rfl

private def ps3 : List ℕ := 5::ps2

private theorem c3 : F ps2 6022026888379=2007342296127 := by decide +kernel
private theorem v3 : F ps3 30110134441897=origin-22080765257391 :=
  transfer (p:=5) (origin:=origin) (removed:=20073422961264) (by decide) v2 c3 rfl (by decide) (by decide) rfl

private def ps4 : List ℕ := 7::ps3

private theorem c4 : F ps3 4301447777413=1147052740644 := by decide +kernel
private theorem v4 : F ps4 30110134441897=origin-23227817998035 :=
  transfer (p:=7) (origin:=origin) (removed:=22080765257391) (by decide) v3 c4 rfl (by decide) (by decide) rfl

private def ps5 : List ℕ := 11::ps4

private theorem c5 : F ps4 2737284949263=625665131260 := by decide +kernel
private theorem v5 : F ps5 30110134441897=origin-23853483129295 :=
  transfer (p:=11) (origin:=origin) (removed:=23227817998035) (by decide) v4 c5 rfl (by decide) (by decide) rfl

private def ps6 : List ℕ := 13::ps5

private theorem v6 : F ps6 30110134441897=origin-24334763999495 := by decide +kernel

private def ps7 : List ℕ := 17::ps6

private theorem c7 : F ps6 1771184378935=339727673083 := by decide +kernel
private theorem v7 : F ps7 30110134441897=origin-24674491672578 :=
  transfer (p:=17) (origin:=origin) (removed:=24334763999495) (by decide) v6 c7 rfl (by decide) (by decide) rfl

private def ps8 : List ℕ := 19::ps7

private theorem c8 : F ps7 1584743917994=286086461544 := by decide +kernel
private theorem v8 : F ps8 30110134441897=origin-24960578134122 :=
  transfer (p:=19) (origin:=origin) (removed:=24674491672578) (by decide) v7 c8 rfl (by decide) (by decide) rfl

private def ps9 : List ℕ := 23::ps8

private theorem c9 : F ps8 1309136280082=223893752510 := by decide +kernel
private theorem v9 : F ps9 30110134441897=origin-25184471886632 :=
  transfer (p:=23) (origin:=origin) (removed:=24960578134122) (by decide) v8 c9 rfl (by decide) (by decide) rfl

private def ps10 : List ℕ := 29::ps9

private theorem c10 : F ps9 1038280497996=169850432937 := by decide +kernel
private theorem v10 : F ps10 30110134441897=origin-25354322319569 :=
  transfer (p:=29) (origin:=origin) (removed:=25184471886632) (by decide) v9 c10 rfl (by decide) (by decide) rfl

private def ps11 : List ℕ := 31::ps10

private theorem c11 : F ps10 971294659416=153413294270 := by decide +kernel
private theorem v11 : F ps11 30110134441897=origin-25507735613839 :=
  transfer (p:=31) (origin:=origin) (removed:=25354322319569) (by decide) v10 c11 rfl (by decide) (by decide) rfl

private def ps12 : List ℕ := 37::ps11

private theorem c12 : F ps11 813787417348=124389157509 := by decide +kernel
private theorem v12 : F ps12 30110134441897=origin-25632124771348 :=
  transfer (p:=37) (origin:=origin) (removed:=25507735613839) (by decide) v11 c12 rfl (by decide) (by decide) rfl

private def ps13 : List ℕ := 41::ps12

private theorem c13 : F ps12 734393522973=109219748065 := by decide +kernel
private theorem v13 : F ps13 30110134441897=origin-25741344519413 :=
  transfer (p:=41) (origin:=origin) (removed:=25632124771348) (by decide) v12 c13 rfl (by decide) (by decide) rfl

private def ps14 : List ℕ := 43::ps13

private theorem c14 : F ps13 700235684695=101599765660 := by decide +kernel
private theorem v14 : F ps14 30110134441897=origin-25842944285073 :=
  transfer (p:=43) (origin:=origin) (removed:=25741344519413) (by decide) v13 c14 rfl (by decide) (by decide) rfl

private def ps15 : List ℕ := 47::ps14

private theorem c15 : F ps14 640641158338=90791279923 := by decide +kernel
private theorem v15 : F ps15 30110134441897=origin-25933735564996 :=
  transfer (p:=47) (origin:=origin) (removed:=25842944285073) (by decide) v14 c15 rfl (by decide) (by decide) rfl

private def ps16 : List ℕ := 53::ps15

private theorem c16 : F ps15 568115744186=78799978784 := by decide +kernel
private theorem v16 : F ps16 30110134441897=origin-26012535543780 :=
  transfer (p:=53) (origin:=origin) (removed:=25933735564996) (by decide) v15 c16 rfl (by decide) (by decide) rfl

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



private def r0_1 : List ℕ := []
private theorem r0_1ok : (List.range' 0 1).filter prime = r0_1 :=
  by decide +kernel

set_option maxRecDepth 20000 in
private theorem row0 :
    ((List.range (0+1)).filter (fun p => decide p.Prime)).reverse = ps0 := by
  rw [filter_from_test prime prime_ok 0 (by decide),List.range_eq_range',r0_1ok]
  rfl

private def r0_54 : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53]
private theorem r0_54ok : (List.range' 0 54).filter prime = r0_54 :=
  by decide +kernel

set_option maxRecDepth 20000 in
private theorem row16 :
    ((List.range (53+1)).filter (fun p => decide p.Prime)).reverse = ps16 := by
  rw [filter_from_test prime prime_ok 53 (by decide),List.range_eq_range',r0_54ok]
  rfl

private theorem bridge {k : ℕ} {ps : List ℕ} (row :
    ((List.range (k+1)).filter (fun p => decide p.Prime)).reverse = ps) :
    ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE k, ¬ p ∣ n)).card = F ps 30110134441897 := by
  calc
    _ = (((List.range (k+1)).filter (fun p => decide p.Prime)).reverse.foldr advance id) 30110134441897 :=
      (legendre_range k 30110134441897).symm
    _ = evalPhi tab ((List.range (k+1)).filter (fun p => decide p.Prime)).reverse 30110134441897 :=
      agree_range tab FastDenseControl.fast_correct k (by decide) 30110134441897
    _ = _ := by rw [row]

set_option maxRecDepth 20000 in
theorem exact_change : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 53, ¬ p ∣ n)).card = ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 0, ¬ p ∣ n)).card - 26012535543780 := by
  exact (bridge row16).trans ((v16).trans (congrArg (fun n : ℕ => n-26012535543780) (bridge row0).symm))
end SieveA30From0To16


open Finset
namespace SieveA30From0To16
theorem survivors : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 53, ¬ p ∣ n)).card=4097598898117 := by
  have base : ((Icc 1 30110134441897).filter (fun n => ∀ p ∈ Nat.primesLE 0, ¬ p ∣ n)).card=30110134441897 := by simp [Nat.primesLE]
  rw [exact_change,base]
end SieveA30From0To16
