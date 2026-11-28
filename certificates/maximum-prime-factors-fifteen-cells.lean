import certificates.«prime-factor-pentomino-pair-2-3»
import certificates.«prime-factor-pentomino-pair-2-4»
import certificates.«prime-factor-pentomino-pair-2-5»
import certificates.«prime-factor-pentomino-pair-2-6»
import certificates.«prime-factor-pentomino-pair-2-7»
import certificates.«prime-factor-pentomino-pair-2-8»
import certificates.«prime-factor-pentomino-pair-2-9»
import certificates.«prime-factor-pentomino-pair-2-10»
import certificates.«prime-factor-pentomino-pair-2-11»
import certificates.«prime-factor-pentomino-pair-2-12»
import certificates.«prime-factor-pentomino-pair-2-13»
import certificates.«prime-factor-pentomino-pair-3-4»
import certificates.«prime-factor-pentomino-pair-3-5»
import certificates.«prime-factor-pentomino-pair-3-6»
import certificates.«prime-factor-pentomino-pair-3-7»
import certificates.«prime-factor-pentomino-pair-3-8»
import certificates.«prime-factor-pentomino-pair-3-9»
import certificates.«prime-factor-pentomino-pair-3-10»
import certificates.«prime-factor-pentomino-pair-3-11»
import certificates.«prime-factor-pentomino-pair-3-12»
import certificates.«prime-factor-pentomino-pair-3-13»
import certificates.«prime-factor-pentomino-pair-4-5»
import certificates.«prime-factor-pentomino-pair-4-6»
import certificates.«prime-factor-pentomino-pair-4-7»
import certificates.«prime-factor-pentomino-pair-4-8»
import certificates.«prime-factor-pentomino-pair-4-9»
import certificates.«prime-factor-pentomino-pair-4-10»
import certificates.«prime-factor-pentomino-pair-4-11»
import certificates.«prime-factor-pentomino-pair-4-12»
import certificates.«prime-factor-pentomino-pair-4-13»
import certificates.«prime-factor-pentomino-pair-5-6»
import certificates.«prime-factor-pentomino-pair-5-7»
import certificates.«prime-factor-pentomino-pair-5-8»
import certificates.«prime-factor-pentomino-pair-5-9»
import certificates.«prime-factor-pentomino-pair-5-10»
import certificates.«prime-factor-pentomino-pair-5-11»
import certificates.«prime-factor-pentomino-pair-5-12»
import certificates.«prime-factor-pentomino-pair-5-13»
import certificates.«prime-factor-pentomino-pair-6-7»
import certificates.«prime-factor-pentomino-pair-6-8»
import certificates.«prime-factor-pentomino-pair-6-9»
import certificates.«prime-factor-pentomino-pair-6-10»
import certificates.«prime-factor-pentomino-pair-6-11»
import certificates.«prime-factor-pentomino-pair-6-12»
import certificates.«prime-factor-pentomino-pair-6-13»
import certificates.«prime-factor-pentomino-pair-7-8»
import certificates.«prime-factor-pentomino-pair-7-9»
import certificates.«prime-factor-pentomino-pair-7-10»
import certificates.«prime-factor-pentomino-pair-7-11»
import certificates.«prime-factor-pentomino-pair-7-12»
import certificates.«prime-factor-pentomino-pair-7-13»
import certificates.«prime-factor-pentomino-pair-8-9»
import certificates.«prime-factor-pentomino-pair-8-10»
import certificates.«prime-factor-pentomino-pair-8-11»
import certificates.«prime-factor-pentomino-pair-8-12»
import certificates.«prime-factor-pentomino-pair-8-13»
import certificates.«prime-factor-pentomino-pair-9-10»
import certificates.«prime-factor-pentomino-pair-9-11»
import certificates.«prime-factor-pentomino-pair-9-12»
import certificates.«prime-factor-pentomino-pair-9-13»
import certificates.«prime-factor-pentomino-pair-10-11»
import certificates.«prime-factor-pentomino-pair-10-12»
import certificates.«prime-factor-pentomino-pair-10-13»
import certificates.«prime-factor-pentomino-pair-11-12»
import certificates.«prime-factor-pentomino-pair-11-13»
import certificates.«prime-factor-pentomino-pair-12-13»

/-!
# Exactly three distinct prime factors are possible on fifteen cells

An explicit board attains three. Any board with at least four factors would
have two noncongruent pentomino factors. The geometric reduction shows that
every such pair can be aligned with one of 66 initial configurations.
The certificates below check all of them.
-/
open OMA.S_oeis_a380455 FactorMaskCheck
namespace PrimePolyFactor

set_option maxRecDepth 12000 in
private theorem anchor2 : boardWord (tileAt 2).shape=61172327507089861859313440401083287816083068462630935381595464136367774636882150025151199014868406506088104258424914476063104058575785394104730774209941392811810242434529742477824496986382989793155481476418603263334799479946050289185598321828837459292181337992549761048182418507352444658247801114419809313895293770358776984311916599642099579617280 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem anchor3 : boardWord (tileAt 3).shape=14242792387281046681877561007306793346162599512945927603605881787513787099152796391257294876087725103162407355784062004865564315496637385079473553841063349000677953669700408650645983642298964451126506311799286141073708778835456355576707447984957797387359922939505442124918447134461456427219054672912642029066901873656909193891930980745216 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem anchor4 : boardWord (tileAt 4).shape=14242792387281046683421767651442727576493720214448446898772941417237809183504268533340610033962653938654374665522041080610054952258083771633923033493740409636900235841743053251048534297020650049198550455245805972052794407967710659250799822642843421518723759350394587616642045166485148850310433640574825956167194085247723758510115605446656 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem anchor5 : boardWord (tileAt 5).shape=3316158520503287138369800987056811755591298206959708751916291163814010840247588987236668234635302591132364561280147817625100889464231419949957477111848982739575192963787933992944561574103714383362465417720202463618419883832078761774016345670056362076265028866728846551361072363800522794420300156182972781833267468535098100416512 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem anchor6 : boardWord (tileAt 6).shape=9948475555333034836048895651038710189942790173106253109787617383516914750581485194002031900661025050587258698348775401533835527856696834231941132027255986815655136460800961618658191822074849782433085854826819556653899275470676705926772430931919260244603721085720566205701540249451844337252903317009033470868849158517816664522752 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem anchor7 : boardWord (tileAt 7).shape=3316158518959080494593405383698154235634639949950454068915864475251000012711133991677204750754337207659802440180472252905894730669524727012597996013255533812518243224664331586978411762881401210468550025943609022725071746062156398653807022903377451428323709596086902993664080962078316423238010720959640002852123616576161923989504 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem anchor8 : boardWord (tileAt 8).shape=3316158523591700427001208074691516340142197835451632958087930728305416438961079465301991257230239136873739667413944163190233890332873165970629177921922380328646177025871983551143468557097533640808109518880865910121834657084433522627463895297468960660991146071257697089735158231352453326224562502260516637624567310430715798093824 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem anchor9 : boardWord (tileAt 9).shape=28485584777878251881169995862554287456884990289202948594890523387154248818685891451314387449769468660310171125632028691653404742842041519955822848034824576614987326264976551896601110475565904559114252896752371402694495633591386992212288839202102883993938980555810664806628617910276394243840838626041849408854435510307432451127100122857472 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem anchor10 : boardWord (tileAt 10).shape=6632317041778677598088491835334257498842133985187337425247402578226835122443115228779870183794584984602884751142910809546444516686202006295618325466551440075200318505219246815738894373543988897342981872524963365325154587692863687801622900676424790832078978037156183170080588896408389879711903292162172804242600794060791616634880 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem anchor11 : boardWord (tileAt 11).shape=19896951111438172993446681163298054367545117917480426140990055017632642943110907642310597515846029903512673025280165977363913793471132834859585635297365448227360205499245302067166154869486259695484222746738197551396113370970059576107135071200150587168756362475139622478761524667711032965377109613814294182313764174026228744847360 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem anchor12 : boardWord (tileAt 12).shape=13264634078152631940263059356619739816242006284658746359566346278069672489407186755735628036923276680061174918600844102258865769392859686945596620555809559568308601463913773344929746006436899410412726579813158275731794448909724018149940911434336451174254641968953155330771450226520262986686584871965485137478667761320943253716992 := by decide +kernel

set_option maxRecDepth 12000 in
private theorem anchor13 : boardWord (tileAt 13).shape=6632317041778677598268261148820489089615064504266239898609200276121065779716545309937602859600085947735593228465318345567564630566073399653277115235365856697693165935858720940116662266968854382619284092126209459444607670644948693570461051358767253713552891147697010407243939407092976177951850538100652520547436150390415840772096 := by decide +kernel

private theorem pair2x3 : pairAt 2 3 := by
  refine ⟨guide2x3,?_⟩
  rw [anchor2]
  exact guided_2_3

private theorem pair2x4 : pairAt 2 4 := by
  refine ⟨guide2x4,?_⟩
  rw [anchor2]
  exact guided_2_4

private theorem pair2x5 : pairAt 2 5 := by
  refine ⟨guide2x5,?_⟩
  rw [anchor2]
  exact guided_2_5

private theorem pair2x6 : pairAt 2 6 := by
  refine ⟨guide2x6,?_⟩
  rw [anchor2]
  exact guided_2_6

private theorem pair2x7 : pairAt 2 7 := by
  refine ⟨guide2x7,?_⟩
  rw [anchor2]
  exact guided_2_7

private theorem pair2x8 : pairAt 2 8 := by
  refine ⟨guide2x8,?_⟩
  rw [anchor2]
  exact guided_2_8

private theorem pair2x9 : pairAt 2 9 := by
  refine ⟨guide2x9,?_⟩
  rw [anchor2]
  exact guided_2_9

private theorem pair2x10 : pairAt 2 10 := by
  refine ⟨guide2x10,?_⟩
  rw [anchor2]
  exact guided_2_10

private theorem pair2x11 : pairAt 2 11 := by
  refine ⟨guide2x11,?_⟩
  rw [anchor2]
  exact guided_2_11

private theorem pair2x12 : pairAt 2 12 := by
  refine ⟨guide2x12,?_⟩
  rw [anchor2]
  exact guided_2_12

private theorem pair2x13 : pairAt 2 13 := by
  refine ⟨guide2x13,?_⟩
  rw [anchor2]
  exact guided_2_13

private theorem pair3x4 : pairAt 3 4 := by
  refine ⟨guide3x4,?_⟩
  rw [anchor3]
  exact guided_3_4

private theorem pair3x5 : pairAt 3 5 := by
  refine ⟨guide3x5,?_⟩
  rw [anchor3]
  exact guided_3_5

private theorem pair3x6 : pairAt 3 6 := by
  refine ⟨guide3x6,?_⟩
  rw [anchor3]
  exact guided_3_6

private theorem pair3x7 : pairAt 3 7 := by
  refine ⟨guide3x7,?_⟩
  rw [anchor3]
  exact guided_3_7

private theorem pair3x8 : pairAt 3 8 := by
  refine ⟨guide3x8,?_⟩
  rw [anchor3]
  exact guided_3_8

private theorem pair3x9 : pairAt 3 9 := by
  refine ⟨guide3x9,?_⟩
  rw [anchor3]
  exact guided_3_9

private theorem pair3x10 : pairAt 3 10 := by
  refine ⟨guide3x10,?_⟩
  rw [anchor3]
  exact guided_3_10

private theorem pair3x11 : pairAt 3 11 := by
  refine ⟨guide3x11,?_⟩
  rw [anchor3]
  exact guided_3_11

private theorem pair3x12 : pairAt 3 12 := by
  refine ⟨guide3x12,?_⟩
  rw [anchor3]
  exact guided_3_12

private theorem pair3x13 : pairAt 3 13 := by
  refine ⟨guide3x13,?_⟩
  rw [anchor3]
  exact guided_3_13

private theorem pair4x5 : pairAt 4 5 := by
  refine ⟨guide4x5,?_⟩
  rw [anchor4]
  exact guided_4_5

private theorem pair4x6 : pairAt 4 6 := by
  refine ⟨guide4x6,?_⟩
  rw [anchor4]
  exact guided_4_6

private theorem pair4x7 : pairAt 4 7 := by
  refine ⟨guide4x7,?_⟩
  rw [anchor4]
  exact guided_4_7

private theorem pair4x8 : pairAt 4 8 := by
  refine ⟨guide4x8,?_⟩
  rw [anchor4]
  exact guided_4_8

private theorem pair4x9 : pairAt 4 9 := by
  refine ⟨guide4x9,?_⟩
  rw [anchor4]
  exact guided_4_9

private theorem pair4x10 : pairAt 4 10 := by
  refine ⟨guide4x10,?_⟩
  rw [anchor4]
  exact guided_4_10

private theorem pair4x11 : pairAt 4 11 := by
  refine ⟨guide4x11,?_⟩
  rw [anchor4]
  exact guided_4_11

private theorem pair4x12 : pairAt 4 12 := by
  refine ⟨guide4x12,?_⟩
  rw [anchor4]
  exact guided_4_12

private theorem pair4x13 : pairAt 4 13 := by
  refine ⟨guide4x13,?_⟩
  rw [anchor4]
  exact guided_4_13

private theorem pair5x6 : pairAt 5 6 := by
  refine ⟨guide5x6,?_⟩
  rw [anchor5]
  exact guided_5_6

private theorem pair5x7 : pairAt 5 7 := by
  refine ⟨guide5x7,?_⟩
  rw [anchor5]
  exact guided_5_7

private theorem pair5x8 : pairAt 5 8 := by
  refine ⟨guide5x8,?_⟩
  rw [anchor5]
  exact guided_5_8

private theorem pair5x9 : pairAt 5 9 := by
  refine ⟨guide5x9,?_⟩
  rw [anchor5]
  exact guided_5_9

private theorem pair5x10 : pairAt 5 10 := by
  refine ⟨guide5x10,?_⟩
  rw [anchor5]
  exact guided_5_10

private theorem pair5x11 : pairAt 5 11 := by
  refine ⟨guide5x11,?_⟩
  rw [anchor5]
  exact guided_5_11

private theorem pair5x12 : pairAt 5 12 := by
  refine ⟨guide5x12,?_⟩
  rw [anchor5]
  exact guided_5_12

private theorem pair5x13 : pairAt 5 13 := by
  refine ⟨guide5x13,?_⟩
  rw [anchor5]
  exact guided_5_13

private theorem pair6x7 : pairAt 6 7 := by
  refine ⟨guide6x7,?_⟩
  rw [anchor6]
  exact guided_6_7

private theorem pair6x8 : pairAt 6 8 := by
  refine ⟨guide6x8,?_⟩
  rw [anchor6]
  exact guided_6_8

private theorem pair6x9 : pairAt 6 9 := by
  refine ⟨guide6x9,?_⟩
  rw [anchor6]
  exact guided_6_9

private theorem pair6x10 : pairAt 6 10 := by
  refine ⟨guide6x10,?_⟩
  rw [anchor6]
  exact guided_6_10

private theorem pair6x11 : pairAt 6 11 := by
  refine ⟨guide6x11,?_⟩
  rw [anchor6]
  exact guided_6_11

private theorem pair6x12 : pairAt 6 12 := by
  refine ⟨guide6x12,?_⟩
  rw [anchor6]
  exact guided_6_12

private theorem pair6x13 : pairAt 6 13 := by
  refine ⟨guide6x13,?_⟩
  rw [anchor6]
  exact guided_6_13

private theorem pair7x8 : pairAt 7 8 := by
  refine ⟨guide7x8,?_⟩
  rw [anchor7]
  exact guided_7_8

private theorem pair7x9 : pairAt 7 9 := by
  refine ⟨guide7x9,?_⟩
  rw [anchor7]
  exact guided_7_9

private theorem pair7x10 : pairAt 7 10 := by
  refine ⟨guide7x10,?_⟩
  rw [anchor7]
  exact guided_7_10

private theorem pair7x11 : pairAt 7 11 := by
  refine ⟨guide7x11,?_⟩
  rw [anchor7]
  exact guided_7_11

private theorem pair7x12 : pairAt 7 12 := by
  refine ⟨guide7x12,?_⟩
  rw [anchor7]
  exact guided_7_12

private theorem pair7x13 : pairAt 7 13 := by
  refine ⟨guide7x13,?_⟩
  rw [anchor7]
  exact guided_7_13

private theorem pair8x9 : pairAt 8 9 := by
  refine ⟨guide8x9,?_⟩
  rw [anchor8]
  exact guided_8_9

private theorem pair8x10 : pairAt 8 10 := by
  refine ⟨guide8x10,?_⟩
  rw [anchor8]
  exact guided_8_10

private theorem pair8x11 : pairAt 8 11 := by
  refine ⟨guide8x11,?_⟩
  rw [anchor8]
  exact guided_8_11

private theorem pair8x12 : pairAt 8 12 := by
  refine ⟨guide8x12,?_⟩
  rw [anchor8]
  exact guided_8_12

private theorem pair8x13 : pairAt 8 13 := by
  refine ⟨guide8x13,?_⟩
  rw [anchor8]
  exact guided_8_13

private theorem pair9x10 : pairAt 9 10 := by
  refine ⟨guide9x10,?_⟩
  rw [anchor9]
  exact guided_9_10

private theorem pair9x11 : pairAt 9 11 := by
  refine ⟨guide9x11,?_⟩
  rw [anchor9]
  exact guided_9_11

private theorem pair9x12 : pairAt 9 12 := by
  refine ⟨guide9x12,?_⟩
  rw [anchor9]
  exact guided_9_12

private theorem pair9x13 : pairAt 9 13 := by
  refine ⟨guide9x13,?_⟩
  rw [anchor9]
  exact guided_9_13

private theorem pair10x11 : pairAt 10 11 := by
  refine ⟨guide10x11,?_⟩
  rw [anchor10]
  exact guided_10_11

private theorem pair10x12 : pairAt 10 12 := by
  refine ⟨guide10x12,?_⟩
  rw [anchor10]
  exact guided_10_12

private theorem pair10x13 : pairAt 10 13 := by
  refine ⟨guide10x13,?_⟩
  rw [anchor10]
  exact guided_10_13

private theorem pair11x12 : pairAt 11 12 := by
  refine ⟨guide11x12,?_⟩
  rw [anchor11]
  exact guided_11_12

private theorem pair11x13 : pairAt 11 13 := by
  refine ⟨guide11x13,?_⟩
  rw [anchor11]
  exact guided_11_13

private theorem pair12x13 : pairAt 12 13 := by
  refine ⟨guide12x13,?_⟩
  rw [anchor12]
  exact guided_12_13

private theorem row2 (j : Fin 14) (order : 2 < j.val) : pairAt 2 j := by
  fin_cases j
  · exact ((by decide : ¬(2 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(2 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(2 : ℕ) < 2) order).elim
  · exact pair2x3
  · exact pair2x4
  · exact pair2x5
  · exact pair2x6
  · exact pair2x7
  · exact pair2x8
  · exact pair2x9
  · exact pair2x10
  · exact pair2x11
  · exact pair2x12
  · exact pair2x13

private theorem row3 (j : Fin 14) (order : 3 < j.val) : pairAt 3 j := by
  fin_cases j
  · exact ((by decide : ¬(3 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(3 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(3 : ℕ) < 2) order).elim
  · exact ((by decide : ¬(3 : ℕ) < 3) order).elim
  · exact pair3x4
  · exact pair3x5
  · exact pair3x6
  · exact pair3x7
  · exact pair3x8
  · exact pair3x9
  · exact pair3x10
  · exact pair3x11
  · exact pair3x12
  · exact pair3x13

private theorem row4 (j : Fin 14) (order : 4 < j.val) : pairAt 4 j := by
  fin_cases j
  · exact ((by decide : ¬(4 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(4 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(4 : ℕ) < 2) order).elim
  · exact ((by decide : ¬(4 : ℕ) < 3) order).elim
  · exact ((by decide : ¬(4 : ℕ) < 4) order).elim
  · exact pair4x5
  · exact pair4x6
  · exact pair4x7
  · exact pair4x8
  · exact pair4x9
  · exact pair4x10
  · exact pair4x11
  · exact pair4x12
  · exact pair4x13

private theorem row5 (j : Fin 14) (order : 5 < j.val) : pairAt 5 j := by
  fin_cases j
  · exact ((by decide : ¬(5 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(5 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(5 : ℕ) < 2) order).elim
  · exact ((by decide : ¬(5 : ℕ) < 3) order).elim
  · exact ((by decide : ¬(5 : ℕ) < 4) order).elim
  · exact ((by decide : ¬(5 : ℕ) < 5) order).elim
  · exact pair5x6
  · exact pair5x7
  · exact pair5x8
  · exact pair5x9
  · exact pair5x10
  · exact pair5x11
  · exact pair5x12
  · exact pair5x13

private theorem row6 (j : Fin 14) (order : 6 < j.val) : pairAt 6 j := by
  fin_cases j
  · exact ((by decide : ¬(6 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(6 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(6 : ℕ) < 2) order).elim
  · exact ((by decide : ¬(6 : ℕ) < 3) order).elim
  · exact ((by decide : ¬(6 : ℕ) < 4) order).elim
  · exact ((by decide : ¬(6 : ℕ) < 5) order).elim
  · exact ((by decide : ¬(6 : ℕ) < 6) order).elim
  · exact pair6x7
  · exact pair6x8
  · exact pair6x9
  · exact pair6x10
  · exact pair6x11
  · exact pair6x12
  · exact pair6x13

private theorem row7 (j : Fin 14) (order : 7 < j.val) : pairAt 7 j := by
  fin_cases j
  · exact ((by decide : ¬(7 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(7 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(7 : ℕ) < 2) order).elim
  · exact ((by decide : ¬(7 : ℕ) < 3) order).elim
  · exact ((by decide : ¬(7 : ℕ) < 4) order).elim
  · exact ((by decide : ¬(7 : ℕ) < 5) order).elim
  · exact ((by decide : ¬(7 : ℕ) < 6) order).elim
  · exact ((by decide : ¬(7 : ℕ) < 7) order).elim
  · exact pair7x8
  · exact pair7x9
  · exact pair7x10
  · exact pair7x11
  · exact pair7x12
  · exact pair7x13

private theorem row8 (j : Fin 14) (order : 8 < j.val) : pairAt 8 j := by
  fin_cases j
  · exact ((by decide : ¬(8 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(8 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(8 : ℕ) < 2) order).elim
  · exact ((by decide : ¬(8 : ℕ) < 3) order).elim
  · exact ((by decide : ¬(8 : ℕ) < 4) order).elim
  · exact ((by decide : ¬(8 : ℕ) < 5) order).elim
  · exact ((by decide : ¬(8 : ℕ) < 6) order).elim
  · exact ((by decide : ¬(8 : ℕ) < 7) order).elim
  · exact ((by decide : ¬(8 : ℕ) < 8) order).elim
  · exact pair8x9
  · exact pair8x10
  · exact pair8x11
  · exact pair8x12
  · exact pair8x13

private theorem row9 (j : Fin 14) (order : 9 < j.val) : pairAt 9 j := by
  fin_cases j
  · exact ((by decide : ¬(9 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(9 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(9 : ℕ) < 2) order).elim
  · exact ((by decide : ¬(9 : ℕ) < 3) order).elim
  · exact ((by decide : ¬(9 : ℕ) < 4) order).elim
  · exact ((by decide : ¬(9 : ℕ) < 5) order).elim
  · exact ((by decide : ¬(9 : ℕ) < 6) order).elim
  · exact ((by decide : ¬(9 : ℕ) < 7) order).elim
  · exact ((by decide : ¬(9 : ℕ) < 8) order).elim
  · exact ((by decide : ¬(9 : ℕ) < 9) order).elim
  · exact pair9x10
  · exact pair9x11
  · exact pair9x12
  · exact pair9x13

private theorem row10 (j : Fin 14) (order : 10 < j.val) : pairAt 10 j := by
  fin_cases j
  · exact ((by decide : ¬(10 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(10 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(10 : ℕ) < 2) order).elim
  · exact ((by decide : ¬(10 : ℕ) < 3) order).elim
  · exact ((by decide : ¬(10 : ℕ) < 4) order).elim
  · exact ((by decide : ¬(10 : ℕ) < 5) order).elim
  · exact ((by decide : ¬(10 : ℕ) < 6) order).elim
  · exact ((by decide : ¬(10 : ℕ) < 7) order).elim
  · exact ((by decide : ¬(10 : ℕ) < 8) order).elim
  · exact ((by decide : ¬(10 : ℕ) < 9) order).elim
  · exact ((by decide : ¬(10 : ℕ) < 10) order).elim
  · exact pair10x11
  · exact pair10x12
  · exact pair10x13

private theorem row11 (j : Fin 14) (order : 11 < j.val) : pairAt 11 j := by
  fin_cases j
  · exact ((by decide : ¬(11 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(11 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(11 : ℕ) < 2) order).elim
  · exact ((by decide : ¬(11 : ℕ) < 3) order).elim
  · exact ((by decide : ¬(11 : ℕ) < 4) order).elim
  · exact ((by decide : ¬(11 : ℕ) < 5) order).elim
  · exact ((by decide : ¬(11 : ℕ) < 6) order).elim
  · exact ((by decide : ¬(11 : ℕ) < 7) order).elim
  · exact ((by decide : ¬(11 : ℕ) < 8) order).elim
  · exact ((by decide : ¬(11 : ℕ) < 9) order).elim
  · exact ((by decide : ¬(11 : ℕ) < 10) order).elim
  · exact ((by decide : ¬(11 : ℕ) < 11) order).elim
  · exact pair11x12
  · exact pair11x13

private theorem row12 (j : Fin 14) (order : 12 < j.val) : pairAt 12 j := by
  fin_cases j
  · exact ((by decide : ¬(12 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 2) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 3) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 4) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 5) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 6) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 7) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 8) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 9) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 10) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 11) order).elim
  · exact ((by decide : ¬(12 : ℕ) < 12) order).elim
  · exact pair12x13

private theorem row13 (j : Fin 14) (order : 13 < j.val) : pairAt 13 j := by
  fin_cases j
  · exact ((by decide : ¬(13 : ℕ) < 0) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 1) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 2) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 3) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 4) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 5) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 6) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 7) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 8) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 9) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 10) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 11) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 12) order).elim
  · exact ((by decide : ¬(13 : ℕ) < 13) order).elim

theorem all_pentomino_pairs : completePairs := by
  apply complete_from_indices
  intro i j big order
  fin_cases i
  · exact ((by decide : ¬2 ≤ (0 : ℕ)) big).elim
  · exact ((by decide : ¬2 ≤ (1 : ℕ)) big).elim
  · exact row2 j order
  · exact row3 j order
  · exact row4 j order
  · exact row5 j order
  · exact row6 j order
  · exact row7 j order
  · exact row8 j order
  · exact row9 j order
  · exact row10 j order
  · exact row11 j order
  · exact row12 j order
  · exact row13 j order

theorem exact_fifteen : maximum 15 3 := by
  refine ⟨achieves_15,?_⟩
  rintro k ⟨board,fs,poly,area,amount,factors,distinct⟩
  rw [←amount]
  exact fifteen_upper_of_pair_checks all_pentomino_pairs poly area factors distinct

end PrimePolyFactor
