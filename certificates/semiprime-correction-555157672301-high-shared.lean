import certificates.«semiprime-correction-204778727327-high»

/-! The high semiprime correction at 555,157,672,301 uses the same prime-count table as the other endpoint proofs. -/
open Finset
namespace SharedCorrectionHigh26

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

private abbrev tab := CheckpointA10425Slim.fast

private abbrev prime := CheckpointA10425Slim.prime
private theorem prime_ok (n : ℕ) (hn : n≤4775000) : prime n=true ↔ n.Prime := CheckpointA10425Slim.prime_ok n hn

private abbrev term := contribution 555157672301 116263 tab prime

private theorem sum_zero (f : ℕ → ℕ) (l : List ℕ) (hf : ∀ p ∈ l, f p=0) :
    (l.map f).sum=0 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,hf p List.mem_cons_self,Nat.zero_add]
    exact ih (fun n h => hf n (List.mem_cons_of_mem p h))

private theorem before : blockSum term 0 116264 0 := by
  apply sum_zero
  intro p hp
  have bound := (List.mem_range'_1.mp hp).2
  have no : ¬ 116263 < p := by omega
  simp [term,contribution,no]

private theorem block116264 : blockSum term 116264 614 15457280 := by unfold blockSum; decide +kernel

private theorem block116878 : blockSum term 116878 614 16661801 := by unfold blockSum; decide +kernel

private theorem block117492 : blockSum term 117492 614 18803650 := by unfold blockSum; decide +kernel

private theorem block118106 : blockSum term 118106 614 15532678 := by unfold blockSum; decide +kernel

private theorem block118720 : blockSum term 118720 614 16398963 := by unfold blockSum; decide +kernel

private theorem block119334 : blockSum term 119334 614 15999840 := by unfold blockSum; decide +kernel

private theorem block119948 : blockSum term 119948 614 15301632 := by unfold blockSum; decide +kernel

private theorem block120562 : blockSum term 120562 614 18949261 := by unfold blockSum; decide +kernel

private theorem block121176 : blockSum term 121176 614 16997666 := by unfold blockSum; decide +kernel

private theorem block121790 : blockSum term 121790 614 16907722 := by unfold blockSum; decide +kernel

private theorem block122404 : blockSum term 122404 614 15602745 := by unfold blockSum; decide +kernel

private theorem block123018 : blockSum term 123018 614 15829129 := by unfold blockSum; decide +kernel

private theorem block123632 : blockSum term 123632 614 15451390 := by unfold blockSum; decide +kernel

private theorem block124246 : blockSum term 124246 614 16880162 := by unfold blockSum; decide +kernel

private theorem block124860 : blockSum term 124860 614 14994286 := by unfold blockSum; decide +kernel

private theorem block125474 : blockSum term 125474 615 16113588 := by unfold blockSum; decide +kernel

private theorem block126089 : blockSum term 126089 614 14552990 := by unfold blockSum; decide +kernel

private theorem block126703 : blockSum term 126703 614 14481082 := by unfold blockSum; decide +kernel

private theorem block127317 : blockSum term 127317 614 16175224 := by unfold blockSum; decide +kernel

private theorem block127931 : blockSum term 127931 614 15511082 := by unfold blockSum; decide +kernel

private theorem block128545 : blockSum term 128545 614 15731229 := by unfold blockSum; decide +kernel

private theorem block129159 : blockSum term 129159 614 16236114 := by unfold blockSum; decide +kernel

private theorem block129773 : blockSum term 129773 614 14137317 := by unfold blockSum; decide +kernel

private theorem block130387 : blockSum term 130387 614 14364064 := by unfold blockSum; decide +kernel

private theorem block131001 : blockSum term 131001 614 14008248 := by unfold blockSum; decide +kernel

private theorem block131615 : blockSum term 131615 614 13945843 := by unfold blockSum; decide +kernel

private theorem block132229 : blockSum term 132229 614 16144431 := by unfold blockSum; decide +kernel

private theorem block132843 : blockSum term 132843 614 15785030 := by unfold blockSum; decide +kernel

private theorem block133457 : blockSum term 133457 614 12904571 := by unfold blockSum; decide +kernel

private theorem block134071 : blockSum term 134071 614 14523449 := by unfold blockSum; decide +kernel

private theorem block134685 : blockSum term 134685 614 13620946 := by unfold blockSum; decide +kernel

private theorem block135299 : blockSum term 135299 615 16328183 := by unfold blockSum; decide +kernel

private theorem block135914 : blockSum term 135914 614 15420832 := by unfold blockSum; decide +kernel

private theorem block136528 : blockSum term 136528 614 13986250 := by unfold blockSum; decide +kernel

private theorem block137142 : blockSum term 137142 614 14468331 := by unfold blockSum; decide +kernel

private theorem block137756 : blockSum term 137756 614 13584537 := by unfold blockSum; decide +kernel

private theorem block138370 : blockSum term 138370 614 14877550 := by unfold blockSum; decide +kernel

private theorem block138984 : blockSum term 138984 614 13191135 := by unfold blockSum; decide +kernel

private theorem block139598 : blockSum term 139598 614 13403840 := by unfold blockSum; decide +kernel

private theorem block140212 : blockSum term 140212 614 14947144 := by unfold blockSum; decide +kernel

private theorem block140826 : blockSum term 140826 614 13818156 := by unfold blockSum; decide +kernel

private theorem block141440 : blockSum term 141440 614 14813734 := by unfold blockSum; decide +kernel

private theorem block142054 : blockSum term 142054 614 12905367 := by unfold blockSum; decide +kernel

private theorem block142668 : blockSum term 142668 614 12061250 := by unfold blockSum; decide +kernel

private theorem block143282 : blockSum term 143282 614 13574658 := by unfold blockSum; decide +kernel

private theorem block143896 : blockSum term 143896 614 11955890 := by unfold blockSum; decide +kernel

private theorem block144510 : blockSum term 144510 614 13199564 := by unfold blockSum; decide +kernel

private theorem block145124 : blockSum term 145124 615 13397459 := by unfold blockSum; decide +kernel

private theorem block145739 : blockSum term 145739 614 13597679 := by unfold blockSum; decide +kernel

private theorem block146353 : blockSum term 146353 614 12517950 := by unfold blockSum; decide +kernel

private theorem block146967 : blockSum term 146967 614 13736020 := by unfold blockSum; decide +kernel

private theorem block147581 : blockSum term 147581 614 12160224 := by unfold blockSum; decide +kernel

private theorem block148195 : blockSum term 148195 614 12612026 := by unfold blockSum; decide +kernel

private theorem block148809 : blockSum term 148809 614 15319754 := by unfold blockSum; decide +kernel

private theorem block149423 : blockSum term 149423 614 12504667 := by unfold blockSum; decide +kernel

private theorem block150037 : blockSum term 150037 615 13697076 := by unfold blockSum; decide +kernel

private theorem block150652 : blockSum term 150652 614 12644211 := by unfold blockSum; decide +kernel

private theorem block151266 : blockSum term 151266 614 14320153 := by unfold blockSum; decide +kernel

private theorem block151880 : blockSum term 151880 614 12540535 := by unfold blockSum; decide +kernel

private theorem block152494 : blockSum term 152494 614 13223707 := by unfold blockSum; decide +kernel

private theorem block153108 : blockSum term 153108 614 11704647 := by unfold blockSum; decide +kernel

private theorem block153722 : blockSum term 153722 614 12625341 := by unfold blockSum; decide +kernel

private theorem block154336 : blockSum term 154336 614 12331092 := by unfold blockSum; decide +kernel

private theorem block154950 : blockSum term 154950 615 11799710 := by unfold blockSum; decide +kernel

private theorem block155565 : blockSum term 155565 614 12714377 := by unfold blockSum; decide +kernel

private theorem block156179 : blockSum term 156179 614 10986385 := by unfold blockSum; decide +kernel

private theorem block156793 : blockSum term 156793 614 13321459 := by unfold blockSum; decide +kernel

private theorem block157407 : blockSum term 157407 614 11847899 := by unfold blockSum; decide +kernel

private theorem block158021 : blockSum term 158021 614 11562429 := by unfold blockSum; decide +kernel

private theorem block158635 : blockSum term 158635 614 10812160 := by unfold blockSum; decide +kernel

private theorem block159249 : blockSum term 159249 614 13110804 := by unfold blockSum; decide +kernel

private theorem block159863 : blockSum term 159863 614 10729790 := by unfold blockSum; decide +kernel

private theorem block160477 : blockSum term 160477 614 13011557 := by unfold blockSum; decide +kernel

private theorem block161091 : blockSum term 161091 614 10876193 := by unfold blockSum; decide +kernel

private theorem block161705 : blockSum term 161705 614 11295373 := by unfold blockSum; decide +kernel

private theorem block162319 : blockSum term 162319 614 12395000 := by unfold blockSum; decide +kernel

private theorem block162933 : blockSum term 162933 614 11204331 := by unfold blockSum; decide +kernel

private theorem block163547 : blockSum term 163547 614 11842972 := by unfold blockSum; decide +kernel

private theorem block164161 : blockSum term 164161 614 11797293 := by unfold blockSum; decide +kernel

private theorem block164775 : blockSum term 164775 615 9714559 := by unfold blockSum; decide +kernel

private theorem block165390 : blockSum term 165390 614 11256909 := by unfold blockSum; decide +kernel

private theorem block166004 : blockSum term 166004 614 10538680 := by unfold blockSum; decide +kernel

private theorem block166618 : blockSum term 166618 614 13178575 := by unfold blockSum; decide +kernel

private theorem block167232 : blockSum term 167232 614 10236388 := by unfold blockSum; decide +kernel

private theorem block167846 : blockSum term 167846 614 10196770 := by unfold blockSum; decide +kernel

private theorem block168460 : blockSum term 168460 614 10378284 := by unfold blockSum; decide +kernel

private theorem block169074 : blockSum term 169074 614 11218466 := by unfold blockSum; decide +kernel

private theorem block169688 : blockSum term 169688 615 12270765 := by unfold blockSum; decide +kernel

private theorem block170303 : blockSum term 170303 614 11787173 := by unfold blockSum; decide +kernel

private theorem block170917 : blockSum term 170917 614 10003647 := by unfold blockSum; decide +kernel

private theorem block171531 : blockSum term 171531 614 11050230 := by unfold blockSum; decide +kernel

private theorem block172145 : blockSum term 172145 614 12733432 := by unfold blockSum; decide +kernel

private theorem block172759 : blockSum term 172759 614 10319175 := by unfold blockSum; decide +kernel

private theorem block173373 : blockSum term 173373 614 10491924 := by unfold blockSum; decide +kernel

private theorem block173987 : blockSum term 173987 614 10881461 := by unfold blockSum; decide +kernel

private theorem block174601 : blockSum term 174601 615 9566772 := by unfold blockSum; decide +kernel

private theorem block175216 : blockSum term 175216 614 9740089 := by unfold blockSum; decide +kernel

private theorem block175830 : blockSum term 175830 614 12868289 := by unfold blockSum; decide +kernel

private theorem block176444 : blockSum term 176444 614 11770477 := by unfold blockSum; decide +kernel

private theorem block177058 : blockSum term 177058 614 8586082 := by unfold blockSum; decide +kernel

private theorem block177672 : blockSum term 177672 614 10431532 := by unfold blockSum; decide +kernel

private theorem block178286 : blockSum term 178286 614 11639628 := by unfold blockSum; decide +kernel

private theorem block178900 : blockSum term 178900 614 11390204 := by unfold blockSum; decide +kernel

private theorem block179514 : blockSum term 179514 614 11967837 := by unfold blockSum; decide +kernel

private theorem block180128 : blockSum term 180128 614 9868189 := by unfold blockSum; decide +kernel

private theorem block180742 : blockSum term 180742 614 8396510 := by unfold blockSum; decide +kernel

private theorem block181356 : blockSum term 181356 614 10202174 := by unfold blockSum; decide +kernel

private theorem block181970 : blockSum term 181970 614 10980898 := by unfold blockSum; decide +kernel

private theorem block182584 : blockSum term 182584 614 10334673 := by unfold blockSum; decide +kernel

private theorem block183198 : blockSum term 183198 614 10700597 := by unfold blockSum; decide +kernel

private theorem block183812 : blockSum term 183812 614 9857403 := by unfold blockSum; decide +kernel

private theorem block184426 : blockSum term 184426 615 10022579 := by unfold blockSum; decide +kernel

private theorem block185041 : blockSum term 185041 614 10785246 := by unfold blockSum; decide +kernel

private theorem block185655 : blockSum term 185655 614 12139167 := by unfold blockSum; decide +kernel

private theorem block186269 : blockSum term 186269 614 9516402 := by unfold blockSum; decide +kernel

private theorem block186883 : blockSum term 186883 614 10667606 := by unfold blockSum; decide +kernel

private theorem block187497 : blockSum term 187497 614 8465951 := by unfold blockSum; decide +kernel

private theorem block188111 : blockSum term 188111 614 10004623 := by unfold blockSum; decide +kernel

private theorem block188725 : blockSum term 188725 614 9384770 := by unfold blockSum; decide +kernel

private theorem block189339 : blockSum term 189339 615 11300430 := by unfold blockSum; decide +kernel

private theorem block189954 : blockSum term 189954 614 8154022 := by unfold blockSum; decide +kernel

private theorem block190568 : blockSum term 190568 614 10640926 := by unfold blockSum; decide +kernel

private theorem block191182 : blockSum term 191182 614 9637095 := by unfold blockSum; decide +kernel

private theorem block191796 : blockSum term 191796 614 10180621 := by unfold blockSum; decide +kernel

private theorem block192410 : blockSum term 192410 614 10335816 := by unfold blockSum; decide +kernel

private theorem block193024 : blockSum term 193024 614 9347510 := by unfold blockSum; decide +kernel

private theorem block193638 : blockSum term 193638 614 9696671 := by unfold blockSum; decide +kernel

private theorem block194252 : blockSum term 194252 615 8335476 := by unfold blockSum; decide +kernel

private theorem block194867 : blockSum term 194867 614 10196329 := by unfold blockSum; decide +kernel

private theorem block195481 : blockSum term 195481 614 9406716 := by unfold blockSum; decide +kernel

private theorem block196095 : blockSum term 196095 614 8625095 := by unfold blockSum; decide +kernel

private theorem block196709 : blockSum term 196709 614 9716080 := by unfold blockSum; decide +kernel

private theorem block197323 : blockSum term 197323 614 9496207 := by unfold blockSum; decide +kernel

private theorem block197937 : blockSum term 197937 614 9648217 := by unfold blockSum; decide +kernel

private theorem block198551 : blockSum term 198551 614 9245937 := by unfold blockSum; decide +kernel

private theorem block199165 : blockSum term 199165 614 9029039 := by unfold blockSum; decide +kernel

private theorem block199779 : blockSum term 199779 614 9550467 := by unfold blockSum; decide +kernel

private theorem block200393 : blockSum term 200393 614 7870338 := by unfold blockSum; decide +kernel

private theorem block201007 : blockSum term 201007 614 8756125 := by unfold blockSum; decide +kernel

private theorem block201621 : blockSum term 201621 614 10364416 := by unfold blockSum; decide +kernel

private theorem block202235 : blockSum term 202235 614 8334766 := by unfold blockSum; decide +kernel

private theorem block202849 : blockSum term 202849 614 9751122 := by unfold blockSum; decide +kernel

private theorem block203463 : blockSum term 203463 614 8098797 := by unfold blockSum; decide +kernel

private theorem block204077 : blockSum term 204077 615 8432138 := by unfold blockSum; decide +kernel

private theorem block204692 : blockSum term 204692 614 8582834 := by unfold blockSum; decide +kernel

private theorem block205306 : blockSum term 205306 614 8734260 := by unfold blockSum; decide +kernel

private theorem block205920 : blockSum term 205920 614 10656910 := by unfold blockSum; decide +kernel

private theorem block206534 : blockSum term 206534 614 7787581 := by unfold blockSum; decide +kernel

private theorem block207148 : blockSum term 207148 614 9879506 := by unfold blockSum; decide +kernel

private theorem block207762 : blockSum term 207762 614 8968407 := by unfold blockSum; decide +kernel

private theorem block208376 : blockSum term 208376 614 8765330 := by unfold blockSum; decide +kernel

private theorem block208990 : blockSum term 208990 614 9781740 := by unfold blockSum; decide +kernel

private theorem block209604 : blockSum term 209604 614 9748634 := by unfold blockSum; decide +kernel

private theorem block210218 : blockSum term 210218 614 8676517 := by unfold blockSum; decide +kernel

private theorem block210832 : blockSum term 210832 614 8992755 := by unfold blockSum; decide +kernel

private theorem block211446 : blockSum term 211446 614 8618946 := by unfold blockSum; decide +kernel

private theorem block212060 : blockSum term 212060 614 7387818 := by unfold blockSum; decide +kernel

private theorem block212674 : blockSum term 212674 614 8390428 := by unfold blockSum; decide +kernel

private theorem block213288 : blockSum term 213288 614 7853527 := by unfold blockSum; decide +kernel

private theorem block213902 : blockSum term 213902 615 9019417 := by unfold blockSum; decide +kernel

private theorem block214517 : blockSum term 214517 614 7973752 := by unfold blockSum; decide +kernel

private theorem block215131 : blockSum term 215131 614 8115248 := by unfold blockSum; decide +kernel

private theorem block215745 : blockSum term 215745 614 7751400 := by unfold blockSum; decide +kernel

private theorem block216359 : blockSum term 216359 614 8229550 := by unfold blockSum; decide +kernel

private theorem block216973 : blockSum term 216973 614 9039719 := by unfold blockSum; decide +kernel

private theorem block217587 : blockSum term 217587 614 7508909 := by unfold blockSum; decide +kernel

private theorem block218201 : blockSum term 218201 614 8316664 := by unfold blockSum; decide +kernel

private theorem block218815 : blockSum term 218815 614 8292376 := by unfold blockSum; decide +kernel

private theorem block219429 : blockSum term 219429 614 10247158 := by unfold blockSum; decide +kernel

private theorem block220043 : blockSum term 220043 614 6918889 := by unfold blockSum; decide +kernel

private theorem block220657 : blockSum term 220657 614 9032903 := by unfold blockSum; decide +kernel

private theorem block221271 : blockSum term 221271 614 7857378 := by unfold blockSum; decide +kernel

private theorem block221885 : blockSum term 221885 614 8159449 := by unfold blockSum; decide +kernel

private theorem block222499 : blockSum term 222499 614 8295087 := by unfold blockSum; decide +kernel

private theorem block223113 : blockSum term 223113 614 8107859 := by unfold blockSum; decide +kernel

private theorem block223727 : blockSum term 223727 615 8081013 := by unfold blockSum; decide +kernel

private theorem block224342 : blockSum term 224342 614 7895165 := by unfold blockSum; decide +kernel

private theorem block224956 : blockSum term 224956 614 8192100 := by unfold blockSum; decide +kernel

private theorem block225570 : blockSum term 225570 614 8006445 := by unfold blockSum; decide +kernel

private theorem block226184 : blockSum term 226184 614 7661260 := by unfold blockSum; decide +kernel

private theorem block226798 : blockSum term 226798 614 7477881 := by unfold blockSum; decide +kernel

private theorem block227412 : blockSum term 227412 614 7773697 := by unfold blockSum; decide +kernel

private theorem block228026 : blockSum term 228026 614 8695837 := by unfold blockSum; decide +kernel

private theorem block228640 : blockSum term 228640 615 8511603 := by unfold blockSum; decide +kernel

private theorem block229255 : blockSum term 229255 614 8955589 := by unfold blockSum; decide +kernel

private theorem block229869 : blockSum term 229869 614 8457405 := by unfold blockSum; decide +kernel

private theorem block230483 : blockSum term 230483 614 7338934 := by unfold blockSum; decide +kernel

private theorem block231097 : blockSum term 231097 614 7782965 := by unfold blockSum; decide +kernel

private theorem block231711 : blockSum term 231711 614 6518899 := by unfold blockSum; decide +kernel

private theorem block232325 : blockSum term 232325 614 7890592 := by unfold blockSum; decide +kernel

private theorem block232939 : blockSum term 232939 614 6477476 := by unfold blockSum; decide +kernel

private theorem block233553 : blockSum term 233553 615 6919558 := by unfold blockSum; decide +kernel

private theorem block234168 : blockSum term 234168 614 8125775 := by unfold blockSum; decide +kernel

private theorem block234782 : blockSum term 234782 614 7489822 := by unfold blockSum; decide +kernel

private theorem block235396 : blockSum term 235396 614 6856132 := by unfold blockSum; decide +kernel

private theorem block236010 : blockSum term 236010 614 6683731 := by unfold blockSum; decide +kernel

private theorem block236624 : blockSum term 236624 614 7875486 := by unfold blockSum; decide +kernel

private theorem block237238 : blockSum term 237238 614 6039735 := by unfold blockSum; decide +kernel

private theorem block237852 : blockSum term 237852 614 8580276 := by unfold blockSum; decide +kernel

private theorem block238466 : blockSum term 238466 614 7203613 := by unfold blockSum; decide +kernel

private theorem block239080 : blockSum term 239080 614 7331571 := by unfold blockSum; decide +kernel

private theorem block239694 : blockSum term 239694 614 7757812 := by unfold blockSum; decide +kernel

private theorem block240308 : blockSum term 240308 614 7138727 := by unfold blockSum; decide +kernel

private theorem block240922 : blockSum term 240922 614 7414184 := by unfold blockSum; decide +kernel

private theorem block241536 : blockSum term 241536 614 8278902 := by unfold blockSum; decide +kernel

private theorem block242150 : blockSum term 242150 614 7221438 := by unfold blockSum; decide +kernel

private theorem block242764 : blockSum term 242764 614 6318977 := by unfold blockSum; decide +kernel

private theorem block243378 : blockSum term 243378 615 7473584 := by unfold blockSum; decide +kernel

private theorem block243993 : blockSum term 243993 614 8179528 := by unfold blockSum; decide +kernel

private theorem block244607 : blockSum term 244607 614 6990131 := by unfold blockSum; decide +kernel

private theorem block245221 : blockSum term 245221 614 7258535 := by unfold blockSum; decide +kernel

private theorem block245835 : blockSum term 245835 614 6946917 := by unfold blockSum; decide +kernel

private theorem block246449 : blockSum term 246449 614 7647695 := by unfold blockSum; decide +kernel

private theorem block247063 : blockSum term 247063 614 6761087 := by unfold blockSum; decide +kernel

private theorem block247677 : blockSum term 247677 614 7746001 := by unfold blockSum; decide +kernel

private theorem block248291 : blockSum term 248291 615 8436486 := by unfold blockSum; decide +kernel

private theorem block248906 : blockSum term 248906 614 6557033 := by unfold blockSum; decide +kernel

private theorem block249520 : blockSum term 249520 614 7248617 := by unfold blockSum; decide +kernel

private theorem block250134 : blockSum term 250134 614 4960031 := by unfold blockSum; decide +kernel

private theorem block250748 : blockSum term 250748 614 8197153 := by unfold blockSum; decide +kernel

private theorem block251362 : blockSum term 251362 614 7326579 := by unfold blockSum; decide +kernel

private theorem block251976 : blockSum term 251976 614 6602357 := by unfold blockSum; decide +kernel

private theorem block252590 : blockSum term 252590 614 6024088 := by unfold blockSum; decide +kernel

private theorem block253204 : blockSum term 253204 615 7401676 := by unfold blockSum; decide +kernel

private theorem block253819 : blockSum term 253819 614 6684992 := by unfold blockSum; decide +kernel

private theorem block254433 : blockSum term 254433 614 6802889 := by unfold blockSum; decide +kernel

private theorem block255047 : blockSum term 255047 614 7614507 := by unfold blockSum; decide +kernel

private theorem block255661 : blockSum term 255661 614 6763597 := by unfold blockSum; decide +kernel

private theorem block256275 : blockSum term 256275 614 5918961 := by unfold blockSum; decide +kernel

private theorem block256889 : blockSum term 256889 614 6861112 := by unfold blockSum; decide +kernel

private theorem block257503 : blockSum term 257503 614 6156308 := by unfold blockSum; decide +kernel

private theorem block258117 : blockSum term 258117 614 7639322 := by unfold blockSum; decide +kernel

private theorem block258731 : blockSum term 258731 614 6121081 := by unfold blockSum; decide +kernel

private theorem block259345 : blockSum term 259345 614 6645344 := by unfold blockSum; decide +kernel

private theorem block259959 : blockSum term 259959 614 6220172 := by unfold blockSum; decide +kernel

private theorem block260573 : blockSum term 260573 614 6472176 := by unfold blockSum; decide +kernel

private theorem block261187 : blockSum term 261187 614 6586831 := by unfold blockSum; decide +kernel

private theorem block261801 : blockSum term 261801 614 6165635 := by unfold blockSum; decide +kernel

private theorem block262415 : blockSum term 262415 614 6015372 := by unfold blockSum; decide +kernel

private theorem block263029 : blockSum term 263029 615 7064136 := by unfold blockSum; decide +kernel

private theorem block263644 : blockSum term 263644 614 6511875 := by unfold blockSum; decide +kernel

private theorem block264258 : blockSum term 264258 614 6359882 := by unfold blockSum; decide +kernel

private theorem block264872 : blockSum term 264872 614 6738636 := by unfold blockSum; decide +kernel

private theorem block265486 : blockSum term 265486 614 6981822 := by unfold blockSum; decide +kernel

private theorem block266100 : blockSum term 266100 614 6304649 := by unfold blockSum; decide +kernel

private theorem block266714 : blockSum term 266714 614 6417778 := by unfold blockSum; decide +kernel

private theorem block267328 : blockSum term 267328 614 8881104 := by unfold blockSum; decide +kernel

private theorem block267942 : blockSum term 267942 615 4948318 := by unfold blockSum; decide +kernel

private theorem block268557 : blockSum term 268557 614 6622582 := by unfold blockSum; decide +kernel

private theorem block269171 : blockSum term 269171 614 6992308 := by unfold blockSum; decide +kernel

private theorem block269785 : blockSum term 269785 614 5937851 := by unfold blockSum; decide +kernel

private theorem block270399 : blockSum term 270399 614 6565947 := by unfold blockSum; decide +kernel

private theorem block271013 : blockSum term 271013 614 6162417 := by unfold blockSum; decide +kernel

private theorem block271627 : blockSum term 271627 614 6144644 := by unfold blockSum; decide +kernel

private theorem block272241 : blockSum term 272241 614 6383881 := by unfold blockSum; decide +kernel

private theorem block272855 : blockSum term 272855 615 5983465 := by unfold blockSum; decide +kernel

private theorem block273470 : blockSum term 273470 614 5584172 := by unfold blockSum; decide +kernel

private theorem block274084 : blockSum term 274084 614 5822769 := by unfold blockSum; decide +kernel

private theorem block274698 : blockSum term 274698 614 6563111 := by unfold blockSum; decide +kernel

private theorem block275312 : blockSum term 275312 614 6418226 := by unfold blockSum; decide +kernel

private theorem block275926 : blockSum term 275926 614 6776204 := by unfold blockSum; decide +kernel

private theorem block276540 : blockSum term 276540 614 5755418 := by unfold blockSum; decide +kernel

private theorem block277154 : blockSum term 277154 614 6113179 := by unfold blockSum; decide +kernel

private theorem block277768 : blockSum term 277768 614 5597681 := by unfold blockSum; decide +kernel

private theorem block278382 : blockSum term 278382 614 6449974 := by unfold blockSum; decide +kernel

private theorem block278996 : blockSum term 278996 614 5565511 := by unfold blockSum; decide +kernel

private theorem block279610 : blockSum term 279610 614 5796885 := by unfold blockSum; decide +kernel

private theorem block280224 : blockSum term 280224 614 6148944 := by unfold blockSum; decide +kernel

private theorem block280838 : blockSum term 280838 614 6499940 := by unfold blockSum; decide +kernel

private theorem block281452 : blockSum term 281452 614 6726212 := by unfold blockSum; decide +kernel

private theorem block282066 : blockSum term 282066 614 5610733 := by unfold blockSum; decide +kernel

private theorem block282680 : blockSum term 282680 615 6081842 := by unfold blockSum; decide +kernel

private theorem block283295 : blockSum term 283295 614 5093811 := by unfold blockSum; decide +kernel

private theorem block283909 : blockSum term 283909 614 6289469 := by unfold blockSum; decide +kernel

private theorem block284523 : blockSum term 284523 614 6634524 := by unfold blockSum; decide +kernel

private theorem block285137 : blockSum term 285137 614 5892910 := by unfold blockSum; decide +kernel

private theorem block285751 : blockSum term 285751 614 4198651 := by unfold blockSum; decide +kernel

private theorem block286365 : blockSum term 286365 614 5981534 := by unfold blockSum; decide +kernel

private theorem block286979 : blockSum term 286979 614 5725980 := by unfold blockSum; decide +kernel

private theorem block287593 : blockSum term 287593 614 4757769 := by unfold blockSum; decide +kernel

private theorem block288207 : blockSum term 288207 614 5574517 := by unfold blockSum; decide +kernel

private theorem block288821 : blockSum term 288821 614 6860174 := by unfold blockSum; decide +kernel

private theorem block289435 : blockSum term 289435 614 6014239 := by unfold blockSum; decide +kernel

private theorem block290049 : blockSum term 290049 614 5761908 := by unfold blockSum; decide +kernel

private theorem block290663 : blockSum term 290663 614 5746093 := by unfold blockSum; decide +kernel

private theorem block291277 : blockSum term 291277 614 5613164 := by unfold blockSum; decide +kernel

private theorem block291891 : blockSum term 291891 614 5364465 := by unfold blockSum; decide +kernel

private theorem block292505 : blockSum term 292505 615 5350611 := by unfold blockSum; decide +kernel

private theorem block293120 : blockSum term 293120 614 5219652 := by unfold blockSum; decide +kernel

private theorem block293734 : blockSum term 293734 614 5897646 := by unfold blockSum; decide +kernel

private theorem block294348 : blockSum term 294348 614 5305126 := by unfold blockSum; decide +kernel

private theorem block294962 : blockSum term 294962 614 5291241 := by unfold blockSum; decide +kernel

private theorem block295576 : blockSum term 295576 614 5276008 := by unfold blockSum; decide +kernel

private theorem block296190 : blockSum term 296190 614 6176453 := by unfold blockSum; decide +kernel

private theorem block296804 : blockSum term 296804 614 4791432 := by unfold blockSum; decide +kernel

private theorem block297418 : blockSum term 297418 614 5573830 := by unfold blockSum; decide +kernel

private theorem block298032 : blockSum term 298032 614 4991460 := by unfold blockSum; decide +kernel

private theorem block298646 : blockSum term 298646 614 5091147 := by unfold blockSum; decide +kernel

private theorem block299260 : blockSum term 299260 614 5415011 := by unfold blockSum; decide +kernel

private theorem block299874 : blockSum term 299874 614 5399597 := by unfold blockSum; decide +kernel

private theorem block300488 : blockSum term 300488 614 6170068 := by unfold blockSum; decide +kernel

private theorem block301102 : blockSum term 301102 614 5704462 := by unfold blockSum; decide +kernel

private theorem block301716 : blockSum term 301716 614 5131387 := by unfold blockSum; decide +kernel

private theorem block302330 : blockSum term 302330 615 4895121 := by unfold blockSum; decide +kernel

private theorem block302945 : blockSum term 302945 614 6213859 := by unfold blockSum; decide +kernel

private theorem block303559 : blockSum term 303559 614 5753373 := by unfold blockSum; decide +kernel

private theorem block304173 : blockSum term 304173 614 5625914 := by unfold blockSum; decide +kernel

private theorem block304787 : blockSum term 304787 614 5501116 := by unfold blockSum; decide +kernel

private theorem block305401 : blockSum term 305401 614 5596531 := by unfold blockSum; decide +kernel

private theorem block306015 : blockSum term 306015 614 5470885 := by unfold blockSum; decide +kernel

private theorem block306629 : blockSum term 306629 614 5346886 := by unfold blockSum; decide +kernel

private theorem block307243 : blockSum term 307243 615 5114761 := by unfold blockSum; decide +kernel

private theorem block307858 : blockSum term 307858 614 4666212 := by unfold blockSum; decide +kernel

private theorem block308472 : blockSum term 308472 614 5410913 := by unfold blockSum; decide +kernel

private theorem block309086 : blockSum term 309086 614 5503957 := by unfold blockSum; decide +kernel

private theorem block309700 : blockSum term 309700 614 4735076 := by unfold blockSum; decide +kernel

private theorem block310314 : blockSum term 310314 614 5366376 := by unfold blockSum; decide +kernel

private theorem block310928 : blockSum term 310928 614 4495879 := by unfold blockSum; decide +kernel

private theorem block311542 : blockSum term 311542 614 4804089 := by unfold blockSum; decide +kernel

private theorem block312156 : blockSum term 312156 615 5855157 := by unfold blockSum; decide +kernel

private theorem block312771 : blockSum term 312771 614 5307279 := by unfold blockSum; decide +kernel

private theorem block313385 : blockSum term 313385 614 5715799 := by unfold blockSum; decide +kernel

private theorem block313999 : blockSum term 313999 614 5172593 := by unfold blockSum; decide +kernel

private theorem block314613 : blockSum term 314613 614 4527259 := by unfold blockSum; decide +kernel

private theorem block315227 : blockSum term 315227 614 5145999 := by unfold blockSum; decide +kernel

private theorem block315841 : blockSum term 315841 614 5237237 := by unfold blockSum; decide +kernel

private theorem block316455 : blockSum term 316455 614 5431831 := by unfold blockSum; decide +kernel

private theorem block317069 : blockSum term 317069 614 5103781 := by unfold blockSum; decide +kernel

private theorem block317683 : blockSum term 317683 614 5504749 := by unfold blockSum; decide +kernel

private theorem block318297 : blockSum term 318297 614 5386021 := by unfold blockSum; decide +kernel

private theorem block318911 : blockSum term 318911 614 5474004 := by unfold blockSum; decide +kernel

private theorem block319525 : blockSum term 319525 614 5356116 := by unfold blockSum; decide +kernel

private theorem block320139 : blockSum term 320139 614 4931347 := by unfold blockSum; decide +kernel

private theorem block320753 : blockSum term 320753 614 4917758 := by unfold blockSum; decide +kernel

private theorem block321367 : blockSum term 321367 614 4802610 := by unfold blockSum; decide +kernel

private theorem block321981 : blockSum term 321981 615 5401033 := by unfold blockSum; decide +kernel

private theorem block322596 : blockSum term 322596 614 4573435 := by unfold blockSum; decide +kernel

private theorem block323210 : blockSum term 323210 614 4662520 := by unfold blockSum; decide +kernel

private theorem block323824 : blockSum term 323824 614 4649778 := by unfold blockSum; decide +kernel

private theorem block324438 : blockSum term 324438 614 5847222 := by unfold blockSum; decide +kernel

private theorem block325052 : blockSum term 325052 614 4524387 := by unfold blockSum; decide +kernel

private theorem block325666 : blockSum term 325666 614 5415365 := by unfold blockSum; decide +kernel

private theorem block326280 : blockSum term 326280 614 4299526 := by unfold blockSum; decide +kernel

private theorem block326894 : blockSum term 326894 615 5184878 := by unfold blockSum; decide +kernel

private theorem block327509 : blockSum term 327509 614 5369947 := by unfold blockSum; decide +kernel

private theorem block328123 : blockSum term 328123 614 4264374 := by unfold blockSum; decide +kernel

private theorem block328737 : blockSum term 328737 614 4945301 := by unfold blockSum; decide +kernel

private theorem block329351 : blockSum term 329351 614 4537488 := by unfold blockSum; decide +kernel

private theorem block329965 : blockSum term 329965 614 4821780 := by unfold blockSum; decide +kernel

private theorem block330579 : blockSum term 330579 614 4808138 := by unfold blockSum; decide +kernel

private theorem block331193 : blockSum term 331193 614 4990317 := by unfold blockSum; decide +kernel

private theorem block331807 : blockSum term 331807 615 4684120 := by unfold blockSum; decide +kernel

private theorem block332422 : blockSum term 332422 614 4379173 := by unfold blockSum; decide +kernel

private theorem block333036 : blockSum term 333036 614 4851843 := by unfold blockSum; decide +kernel

private theorem block333650 : blockSum term 333650 614 4452203 := by unfold blockSum; decide +kernel

private theorem block334264 : blockSum term 334264 614 4729835 := by unfold blockSum; decide +kernel

private theorem block334878 : blockSum term 334878 614 4717630 := by unfold blockSum; decide +kernel

private theorem block335492 : blockSum term 335492 614 4224415 := by unfold blockSum; decide +kernel

private theorem block336106 : blockSum term 336106 614 4978661 := by unfold blockSum; decide +kernel

private theorem block336720 : blockSum term 336720 614 4774595 := by unfold blockSum; decide +kernel

private theorem block337334 : blockSum term 337334 614 4761281 := by unfold blockSum; decide +kernel

private theorem block337948 : blockSum term 337948 614 4938166 := by unfold blockSum; decide +kernel

private theorem block338562 : blockSum term 338562 614 4167969 := by unfold blockSum; decide +kernel

private theorem block339176 : blockSum term 339176 614 3873661 := by unfold blockSum; decide +kernel

private theorem block339790 : blockSum term 339790 614 4334263 := by unfold blockSum; decide +kernel

private theorem block340404 : blockSum term 340404 614 4886190 := by unfold blockSum; decide +kernel

private theorem block341018 : blockSum term 341018 614 4497621 := by unfold blockSum; decide +kernel

private theorem block341632 : blockSum term 341632 615 4578704 := by unfold blockSum; decide +kernel

private theorem block342247 : blockSum term 342247 614 4380477 := by unfold blockSum; decide +kernel

private theorem block342861 : blockSum term 342861 614 4275383 := by unfold blockSum; decide +kernel

private theorem block343475 : blockSum term 343475 614 4449890 := by unfold blockSum; decide +kernel

private theorem block344089 : blockSum term 344089 614 4623288 := by unfold blockSum; decide +kernel

private theorem block344703 : blockSum term 344703 614 4334039 := by unfold blockSum; decide +kernel

private theorem block345317 : blockSum term 345317 614 4597726 := by unfold blockSum; decide +kernel

private theorem block345931 : blockSum term 345931 614 4676768 := by unfold blockSum; decide +kernel

private theorem block346545 : blockSum term 346545 615 4298018 := by unfold blockSum; decide +kernel

private theorem block347160 : blockSum term 347160 614 4378036 := by unfold blockSum; decide +kernel

private theorem block347774 : blockSum term 347774 614 4275330 := by unfold blockSum; decide +kernel

private theorem block348388 : blockSum term 348388 614 4536256 := by unfold blockSum; decide +kernel

private theorem block349002 : blockSum term 349002 614 4523775 := by unfold blockSum; decide +kernel

private theorem block349616 : blockSum term 349616 614 4241047 := by unfold blockSum; decide +kernel

private theorem block350230 : blockSum term 350230 614 4139609 := by unfold blockSum; decide +kernel

private theorem block350844 : blockSum term 350844 614 4847016 := by unfold blockSum; decide +kernel

private theorem block351458 : blockSum term 351458 615 4117836 := by unfold blockSum; decide +kernel

private theorem block352073 : blockSum term 352073 614 4642868 := by unfold blockSum; decide +kernel

private theorem block352687 : blockSum term 352687 614 4007109 := by unfold blockSum; decide +kernel

private theorem block353301 : blockSum term 353301 614 4439772 := by unfold blockSum; decide +kernel

private theorem block353915 : blockSum term 353915 614 4694032 := by unfold blockSum; decide +kernel

private theorem block354529 : blockSum term 354529 614 4945255 := by unfold blockSum; decide +kernel

private theorem block355143 : blockSum term 355143 614 3787060 := by unfold blockSum; decide +kernel

private theorem block355757 : blockSum term 355757 614 3777964 := by unfold blockSum; decide +kernel

private theorem block356371 : blockSum term 356371 614 3592224 := by unfold blockSum; decide +kernel

private theorem block356985 : blockSum term 356985 614 4106805 := by unfold blockSum; decide +kernel

private theorem block357599 : blockSum term 357599 614 4096655 := by unfold blockSum; decide +kernel

private theorem block358213 : blockSum term 358213 614 4606591 := by unfold blockSum; decide +kernel

private theorem block358827 : blockSum term 358827 614 4593685 := by unfold blockSum; decide +kernel

private theorem block359441 : blockSum term 359441 614 3544458 := by unfold blockSum; decide +kernel

private theorem block360055 : blockSum term 360055 614 3449063 := by unfold blockSum; decide +kernel

private theorem block360669 : blockSum term 360669 614 3611681 := by unfold blockSum; decide +kernel

private theorem block361283 : blockSum term 361283 615 4202750 := by unfold blockSum; decide +kernel

private theorem block361898 : blockSum term 361898 614 4704482 := by unfold blockSum; decide +kernel

private theorem block362512 : blockSum term 362512 614 3497703 := by unfold blockSum; decide +kernel

private theorem block363126 : blockSum term 363126 614 4424855 := by unfold blockSum; decide +kernel

private theorem block363740 : blockSum term 363740 614 4158501 := by unfold blockSum; decide +kernel

private theorem block364354 : blockSum term 364354 614 4062487 := by unfold blockSum; decide +kernel

private theorem block364968 : blockSum term 364968 614 4473612 := by unfold blockSum; decide +kernel

private theorem block365582 : blockSum term 365582 614 3788260 := by unfold blockSum; decide +kernel

private theorem block366196 : blockSum term 366196 615 4030831 := by unfold blockSum; decide +kernel

private theorem block366811 : blockSum term 366811 614 4438477 := by unfold blockSum; decide +kernel

private theorem block367425 : blockSum term 367425 614 3925054 := by unfold blockSum; decide +kernel

private theorem block368039 : blockSum term 368039 614 4080796 := by unfold blockSum; decide +kernel

private theorem block368653 : blockSum term 368653 614 3487808 := by unfold blockSum; decide +kernel

private theorem block369267 : blockSum term 369267 614 3064291 := by unfold blockSum; decide +kernel

private theorem block369881 : blockSum term 369881 614 3964933 := by unfold blockSum; decide +kernel

private theorem block370495 : blockSum term 370495 614 3295972 := by unfold blockSum; decide +kernel

private theorem block371109 : blockSum term 371109 615 3944864 := by unfold blockSum; decide +kernel

private theorem block371724 : blockSum term 371724 614 3769398 := by unfold blockSum; decide +kernel

private theorem block372338 : blockSum term 372338 614 4249250 := by unfold blockSum; decide +kernel

private theorem block372952 : blockSum term 372952 614 3830202 := by unfold blockSum; decide +kernel

private theorem block373566 : blockSum term 373566 614 3819708 := by unfold blockSum; decide +kernel

private theorem block374180 : blockSum term 374180 614 3647360 := by unfold blockSum; decide +kernel

private theorem block374794 : blockSum term 374794 614 4688607 := by unfold blockSum; decide +kernel

private theorem block375408 : blockSum term 375408 614 4030158 := by unfold blockSum; decide +kernel

private theorem block376022 : blockSum term 376022 614 3536680 := by unfold blockSum; decide +kernel

private theorem block376636 : blockSum term 376636 614 3848796 := by unfold blockSum; decide +kernel

private theorem block377250 : blockSum term 377250 614 3917921 := by unfold blockSum; decide +kernel

private theorem block377864 : blockSum term 377864 614 3269825 := by unfold blockSum; decide +kernel

private theorem block378478 : blockSum term 378478 614 3977214 := by unfold blockSum; decide +kernel

private theorem block379092 : blockSum term 379092 614 4045384 := by unfold blockSum; decide +kernel

private theorem block379706 : blockSum term 379706 614 3796511 := by unfold blockSum; decide +kernel

private theorem block380320 : blockSum term 380320 614 3392246 := by unfold blockSum; decide +kernel

private theorem block380934 : blockSum term 380934 615 4012656 := by unfold blockSum; decide +kernel

private theorem block381549 : blockSum term 381549 614 3138545 := by unfold blockSum; decide +kernel

private theorem block382163 : blockSum term 382163 614 3677718 := by unfold blockSum; decide +kernel

private theorem block382777 : blockSum term 382777 614 3590256 := by unfold blockSum; decide +kernel

private theorem block383391 : blockSum term 383391 614 4125080 := by unfold blockSum; decide +kernel

private theorem block384005 : blockSum term 384005 614 3880659 := by unfold blockSum; decide +kernel

private theorem block384619 : blockSum term 384619 614 3638103 := by unfold blockSum; decide +kernel

private theorem block385233 : blockSum term 385233 614 3782711 := by unfold blockSum; decide +kernel

private theorem block385847 : blockSum term 385847 615 4002998 := by unfold blockSum; decide +kernel

private theorem block386462 : blockSum term 386462 614 3224693 := by unfold blockSum; decide +kernel

private theorem block387076 : blockSum term 387076 614 3368871 := by unfold blockSum; decide +kernel

private theorem block387690 : blockSum term 387690 614 3435475 := by unfold blockSum; decide +kernel

private theorem block388304 : blockSum term 388304 614 3350304 := by unfold blockSum; decide +kernel

private theorem block388918 : blockSum term 388918 614 3645247 := by unfold blockSum; decide +kernel

private theorem block389532 : blockSum term 389532 614 4013277 := by unfold blockSum; decide +kernel

private theorem block390146 : blockSum term 390146 614 3926680 := by unfold blockSum; decide +kernel

private theorem block390760 : blockSum term 390760 615 3689883 := by unfold blockSum; decide +kernel

private theorem block391375 : blockSum term 391375 614 3529951 := by unfold blockSum; decide +kernel

private theorem block391989 : blockSum term 391989 614 4120196 := by unfold blockSum; decide +kernel

private theorem block392603 : blockSum term 392603 614 4034185 := by unfold blockSum; decide +kernel

private theorem block393217 : blockSum term 393217 614 3724880 := by unfold blockSum; decide +kernel

private theorem block393831 : blockSum term 393831 614 3343621 := by unfold blockSum; decide +kernel

private theorem block394445 : blockSum term 394445 614 3630634 := by unfold blockSum; decide +kernel

private theorem block395059 : blockSum term 395059 614 3547424 := by unfold blockSum; decide +kernel

private theorem block395673 : blockSum term 395673 614 3095642 := by unfold blockSum; decide +kernel

private theorem block396287 : blockSum term 396287 614 3235215 := by unfold blockSum; decide +kernel

private theorem block396901 : blockSum term 396901 614 3445536 := by unfold blockSum; decide +kernel

private theorem block397515 : blockSum term 397515 614 3654429 := by unfold blockSum; decide +kernel

private theorem block398129 : blockSum term 398129 614 3789796 := by unfold blockSum; decide +kernel

private theorem block398743 : blockSum term 398743 614 3270872 := by unfold blockSum; decide +kernel

private theorem block399357 : blockSum term 399357 614 3624564 := by unfold blockSum; decide +kernel

private theorem block399971 : blockSum term 399971 614 3181282 := by unfold blockSum; decide +kernel

private theorem block400585 : blockSum term 400585 615 3100226 := by unfold blockSum; decide +kernel

private theorem block401200 : blockSum term 401200 614 3020483 := by unfold blockSum; decide +kernel

private theorem block401814 : blockSum term 401814 614 3585839 := by unfold blockSum; decide +kernel

private theorem block402428 : blockSum term 402428 614 3146742 := by unfold blockSum; decide +kernel

private theorem block403042 : blockSum term 403042 614 3209216 := by unfold blockSum; decide +kernel

private theorem block403656 : blockSum term 403656 614 3555640 := by unfold blockSum; decide +kernel

private theorem block404270 : blockSum term 404270 614 2837290 := by unfold blockSum; decide +kernel

private theorem block404884 : blockSum term 404884 614 3253844 := by unfold blockSum; decide +kernel

private theorem block405498 : blockSum term 405498 615 3527363 := by unfold blockSum; decide +kernel

private theorem block406113 : blockSum term 406113 614 3235837 := by unfold blockSum; decide +kernel

private theorem block406727 : blockSum term 406727 614 2876166 := by unfold blockSum; decide +kernel

private theorem block407341 : blockSum term 407341 614 3498459 := by unfold blockSum; decide +kernel

private theorem block407955 : blockSum term 407955 614 3558393 := by unfold blockSum; decide +kernel

private theorem block408569 : blockSum term 408569 614 3200775 := by unfold blockSum; decide +kernel

private theorem block409183 : blockSum term 409183 614 3330665 := by unfold blockSum; decide +kernel

private theorem block409797 : blockSum term 409797 614 3598150 := by unfold blockSum; decide +kernel

private theorem block410411 : blockSum term 410411 615 3174237 := by unfold blockSum; decide +kernel

private theorem block411026 : blockSum term 411026 614 3371699 := by unfold blockSum; decide +kernel

private theorem block411640 : blockSum term 411640 614 3842775 := by unfold blockSum; decide +kernel

private theorem block412254 : blockSum term 412254 614 2600799 := by unfold blockSum; decide +kernel

private theorem block412868 : blockSum term 412868 614 2935563 := by unfold blockSum; decide +kernel

private theorem block413482 : blockSum term 413482 614 2927166 := by unfold blockSum; decide +kernel

private theorem block414096 : blockSum term 414096 614 3801034 := by unfold blockSum; decide +kernel

private theorem block414710 : blockSum term 414710 614 3384330 := by unfold blockSum; decide +kernel

private theorem block415324 : blockSum term 415324 614 3172041 := by unfold blockSum; decide +kernel

private theorem block415938 : blockSum term 415938 614 3432715 := by unfold blockSum; decide +kernel

private theorem block416552 : blockSum term 416552 614 2416394 := by unfold blockSum; decide +kernel

private theorem block417166 : blockSum term 417166 614 3548213 := by unfold blockSum; decide +kernel

private theorem block417780 : blockSum term 417780 614 3538039 := by unfold blockSum; decide +kernel

private theorem block418394 : blockSum term 418394 614 3261617 := by unfold blockSum; decide +kernel

private theorem block419008 : blockSum term 419008 614 3319116 := by unfold blockSum; decide +kernel

private theorem block419622 : blockSum term 419622 614 2515688 := by unfold blockSum; decide +kernel

private theorem block420236 : blockSum term 420236 615 3366931 := by unfold blockSum; decide +kernel

private theorem block420851 : blockSum term 420851 614 3094040 := by unfold blockSum; decide +kernel

private theorem block421465 : blockSum term 421465 614 2822816 := by unfold blockSum; decide +kernel

private theorem block422079 : blockSum term 422079 614 3011923 := by unfold blockSum; decide +kernel

private theorem block422693 : blockSum term 422693 614 3590791 := by unfold blockSum; decide +kernel

private theorem block423307 : blockSum term 423307 614 3059843 := by unfold blockSum; decide +kernel

private theorem block423921 : blockSum term 423921 614 3116208 := by unfold blockSum; decide +kernel

private theorem block424535 : blockSum term 424535 614 3236943 := by unfold blockSum; decide +kernel

private theorem block425149 : blockSum term 425149 615 2711788 := by unfold blockSum; decide +kernel

private theorem block425764 : blockSum term 425764 614 2833189 := by unfold blockSum; decide +kernel

private theorem block426378 : blockSum term 426378 614 3017341 := by unfold blockSum; decide +kernel

private theorem block426992 : blockSum term 426992 614 3200908 := by unfold blockSum; decide +kernel

private theorem block427606 : blockSum term 427606 614 2936700 := by unfold blockSum; decide +kernel

private theorem block428220 : blockSum term 428220 614 2928509 := by unfold blockSum; decide +kernel

private theorem block428834 : blockSum term 428834 614 2666432 := by unfold blockSum; decide +kernel

private theorem block429448 : blockSum term 429448 614 3862213 := by unfold blockSum; decide +kernel

private theorem block430062 : blockSum term 430062 615 2273043 := by unfold blockSum; decide +kernel

private theorem block430677 : blockSum term 430677 614 3651996 := by unfold blockSum; decide +kernel

private theorem block431291 : blockSum term 431291 614 3075433 := by unfold blockSum; decide +kernel

private theorem block431905 : blockSum term 431905 614 3379472 := by unfold blockSum; decide +kernel

private theorem block432519 : blockSum term 432519 614 2995493 := by unfold blockSum; decide +kernel

private theorem block433133 : blockSum term 433133 614 3111345 := by unfold blockSum; decide +kernel

private theorem block433747 : blockSum term 433747 614 2916204 := by unfold blockSum; decide +kernel

private theorem block434361 : blockSum term 434361 614 3279138 := by unfold blockSum; decide +kernel

private theorem block434975 : blockSum term 434975 614 3146275 := by unfold blockSum; decide +kernel

private theorem block435589 : blockSum term 435589 614 2953596 := by unfold blockSum; decide +kernel

private theorem block436203 : blockSum term 436203 614 2760937 := by unfold blockSum; decide +kernel

private theorem block436817 : blockSum term 436817 614 2752929 := by unfold blockSum; decide +kernel

private theorem block437431 : blockSum term 437431 614 2562333 := by unfold blockSum; decide +kernel

private theorem block438045 : blockSum term 438045 614 2676544 := by unfold blockSum; decide +kernel

private theorem block438659 : blockSum term 438659 614 2547710 := by unfold blockSum; decide +kernel

private theorem block439273 : blockSum term 439273 614 3144971 := by unfold blockSum; decide +kernel

private theorem block439887 : blockSum term 439887 615 2834435 := by unfold blockSum; decide +kernel

private theorem block440502 : blockSum term 440502 614 3127117 := by unfold blockSum; decide +kernel

private theorem block441116 : blockSum term 441116 614 2578149 := by unfold blockSum; decide +kernel

private theorem block441730 : blockSum term 441730 614 2989016 := by unfold blockSum; decide +kernel

private theorem block442344 : blockSum term 442344 614 2741735 := by unfold blockSum; decide +kernel

private theorem block442958 : blockSum term 442958 614 3566190 := by unfold blockSum; decide +kernel

private theorem block443572 : blockSum term 443572 614 3081406 := by unfold blockSum; decide +kernel

private theorem block444186 : blockSum term 444186 614 2718030 := by unfold blockSum; decide +kernel

private theorem block444800 : blockSum term 444800 614 2651561 := by unfold blockSum; decide +kernel

private theorem block445414 : blockSum term 445414 614 2584589 := by unfold blockSum; decide +kernel

private theorem block446028 : blockSum term 446028 614 2518669 := by unfold blockSum; decide +kernel

private theorem block446642 : blockSum term 446642 614 2511470 := by unfold blockSum; decide +kernel

private theorem block447256 : blockSum term 447256 614 2562879 := by unfold blockSum; decide +kernel

private theorem block447870 : blockSum term 447870 614 2555705 := by unfold blockSum; decide +kernel

private theorem block448484 : blockSum term 448484 614 2374223 := by unfold blockSum; decide +kernel

private theorem block449098 : blockSum term 449098 614 3118796 := by unfold blockSum; decide +kernel

private theorem block449712 : blockSum term 449712 615 2879323 := by unfold blockSum; decide +kernel

private theorem block450327 : blockSum term 450327 614 3273258 := by unfold blockSum; decide +kernel

private theorem block450941 : blockSum term 450941 614 2461980 := by unfold blockSum; decide +kernel

private theorem block451555 : blockSum term 451555 614 2797510 := by unfold blockSum; decide +kernel

private theorem block452169 : blockSum term 452169 614 2220415 := by unfold blockSum; decide +kernel

private theorem block452783 : blockSum term 452783 614 2497553 := by unfold blockSum; decide +kernel

private theorem block453397 : blockSum term 453397 614 2377347 := by unfold blockSum; decide +kernel

private theorem block454011 : blockSum term 454011 614 2540364 := by unfold blockSum; decide +kernel

private theorem block454625 : blockSum term 454625 614 2589369 := by unfold blockSum; decide +kernel

private theorem block455239 : blockSum term 455239 614 2918700 := by unfold blockSum; decide +kernel

private theorem block455853 : blockSum term 455853 614 2406360 := by unfold blockSum; decide +kernel

private theorem block456467 : blockSum term 456467 614 2734294 := by unfold blockSum; decide +kernel

private theorem block457081 : blockSum term 457081 614 2892631 := by unfold blockSum; decide +kernel

private theorem block457695 : blockSum term 457695 614 1996624 := by unfold blockSum; decide +kernel

private theorem block458309 : blockSum term 458309 614 2598974 := by unfold blockSum; decide +kernel

private theorem block458923 : blockSum term 458923 614 2867046 := by unfold blockSum; decide +kernel

private theorem block459537 : blockSum term 459537 615 2144148 := by unfold blockSum; decide +kernel

private theorem block460152 : blockSum term 460152 614 2248097 := by unfold blockSum; decide +kernel

private theorem block460766 : blockSum term 460766 614 2788743 := by unfold blockSum; decide +kernel

private theorem block461380 : blockSum term 461380 614 2235521 := by unfold blockSum; decide +kernel

private theorem block461994 : blockSum term 461994 614 2446296 := by unfold blockSum; decide +kernel

private theorem block462608 : blockSum term 462608 614 2168786 := by unfold blockSum; decide +kernel

private theorem block463222 : blockSum term 463222 614 2811040 := by unfold blockSum; decide +kernel

private theorem block463836 : blockSum term 463836 614 2748580 := by unfold blockSum; decide +kernel

private theorem block464450 : blockSum term 464450 615 2901325 := by unfold blockSum; decide +kernel

private theorem block465065 : blockSum term 465065 614 2464427 := by unfold blockSum; decide +kernel

private theorem block465679 : blockSum term 465679 614 2456623 := by unfold blockSum; decide +kernel

private theorem block466293 : blockSum term 466293 614 2076872 := by unfold blockSum; decide +kernel

private theorem block466907 : blockSum term 466907 614 2442288 := by unfold blockSum; decide +kernel

private theorem block467521 : blockSum term 467521 614 3017022 := by unfold blockSum; decide +kernel

private theorem block468135 : blockSum term 468135 614 2690811 := by unfold blockSum; decide +kernel

private theorem block468749 : blockSum term 468749 614 2314589 := by unfold blockSum; decide +kernel

private theorem block469363 : blockSum term 469363 615 2412506 := by unfold blockSum; decide +kernel

private theorem block469978 : blockSum term 469978 614 2770806 := by unfold blockSum; decide +kernel

private theorem block470592 : blockSum term 470592 614 2605743 := by unfold blockSum; decide +kernel

private theorem block471206 : blockSum term 471206 614 2597071 := by unfold blockSum; decide +kernel

private theorem block471820 : blockSum term 471820 614 2537293 := by unfold blockSum; decide +kernel

private theorem block472434 : blockSum term 472434 614 2116657 := by unfold blockSum; decide +kernel

private theorem block473048 : blockSum term 473048 614 2573682 := by unfold blockSum; decide +kernel

private theorem block473662 : blockSum term 473662 614 2360776 := by unfold blockSum; decide +kernel

private theorem block474276 : blockSum term 474276 614 2405098 := by unfold blockSum; decide +kernel

private theorem block474890 : blockSum term 474890 614 2652641 := by unfold blockSum; decide +kernel

private theorem block475504 : blockSum term 475504 614 2999873 := by unfold blockSum; decide +kernel

private theorem block476118 : blockSum term 476118 614 2179534 := by unfold blockSum; decide +kernel

private theorem block476732 : blockSum term 476732 614 2072314 := by unfold blockSum; decide +kernel

private theorem block477346 : blockSum term 477346 614 2216407 := by unfold blockSum; decide +kernel

private theorem block477960 : blockSum term 477960 614 2460438 := by unfold blockSum; decide +kernel

private theorem block478574 : blockSum term 478574 614 2403290 := by unfold blockSum; decide +kernel

private theorem block479188 : blockSum term 479188 615 2345788 := by unfold blockSum; decide +kernel

private theorem block479803 : blockSum term 479803 614 2437637 := by unfold blockSum; decide +kernel

private theorem block480417 : blockSum term 480417 614 2330691 := by unfold blockSum; decide +kernel

private theorem block481031 : blockSum term 481031 614 2323893 := by unfold blockSum; decide +kernel

private theorem block481645 : blockSum term 481645 614 2316707 := by unfold blockSum; decide +kernel

private theorem block482259 : blockSum term 482259 614 2652737 := by unfold blockSum; decide +kernel

private theorem block482873 : blockSum term 482873 614 2056682 := by unfold blockSum; decide +kernel

private theorem block483487 : blockSum term 483487 614 2343970 := by unfold blockSum; decide +kernel

private theorem block484101 : blockSum term 484101 615 2141924 := by unfold blockSum; decide +kernel

private theorem block484716 : blockSum term 484716 614 1650365 := by unfold blockSum; decide +kernel

private theorem block485330 : blockSum term 485330 614 1936175 := by unfold blockSum; decide +kernel

private theorem block485944 : blockSum term 485944 614 2316329 := by unfold blockSum; decide +kernel

private theorem block486558 : blockSum term 486558 614 2357343 := by unfold blockSum; decide +kernel

private theorem block487172 : blockSum term 487172 614 2397691 := by unfold blockSum; decide +kernel

private theorem block487786 : blockSum term 487786 614 2533633 := by unfold blockSum; decide +kernel

private theorem block488400 : blockSum term 488400 614 2287473 := by unfold blockSum; decide +kernel

private theorem block489014 : blockSum term 489014 615 2090294 := by unfold blockSum; decide +kernel

private theorem block489629 : blockSum term 489629 614 2415040 := by unfold blockSum; decide +kernel

private theorem block490243 : blockSum term 490243 614 2124112 := by unfold blockSum; decide +kernel

private theorem block490857 : blockSum term 490857 614 2258504 := by unfold blockSum; decide +kernel

private theorem block491471 : blockSum term 491471 614 2485492 := by unfold blockSum; decide +kernel

private theorem block492085 : blockSum term 492085 614 1729263 := by unfold blockSum; decide +kernel

private theorem block492699 : blockSum term 492699 614 2329950 := by unfold blockSum; decide +kernel

private theorem block493313 : blockSum term 493313 614 2044115 := by unfold blockSum; decide +kernel

private theorem block493927 : blockSum term 493927 614 2222977 := by unfold blockSum; decide +kernel

private theorem block494541 : blockSum term 494541 614 2401071 := by unfold blockSum; decide +kernel

private theorem block495155 : blockSum term 495155 614 2438760 := by unfold blockSum; decide +kernel

private theorem block495769 : blockSum term 495769 614 2156107 := by unfold blockSum; decide +kernel

private theorem block496383 : blockSum term 496383 614 1829294 := by unfold blockSum; decide +kernel

private theorem block496997 : blockSum term 496997 614 2370538 := by unfold blockSum; decide +kernel

private theorem block497611 : blockSum term 497611 614 1999484 := by unfold blockSum; decide +kernel

private theorem block498225 : blockSum term 498225 614 2128954 := by unfold blockSum; decide +kernel

private theorem block498839 : blockSum term 498839 615 2167251 := by unfold blockSum; decide +kernel

private theorem block499454 : blockSum term 499454 614 2205038 := by unfold blockSum; decide +kernel

private theorem block500068 : blockSum term 500068 614 2152945 := by unfold blockSum; decide +kernel

private theorem block500682 : blockSum term 500682 614 2458093 := by unfold blockSum; decide +kernel

private theorem block501296 : blockSum term 501296 614 1737390 := by unfold blockSum; decide +kernel

private theorem block501910 : blockSum term 501910 614 1865221 := by unfold blockSum; decide +kernel

private theorem block502524 : blockSum term 502524 614 1770651 := by unfold blockSum; decide +kernel

private theorem block503138 : blockSum term 503138 614 1985721 := by unfold blockSum; decide +kernel

private theorem block503752 : blockSum term 503752 615 2286780 := by unfold blockSum; decide +kernel

private theorem block504367 : blockSum term 504367 614 1928522 := by unfold blockSum; decide +kernel

private theorem block504981 : blockSum term 504981 614 2359269 := by unfold blockSum; decide +kernel

private theorem block505595 : blockSum term 505595 614 1916368 := by unfold blockSum; decide +kernel

private theorem block506209 : blockSum term 506209 614 2126964 := by unfold blockSum; decide +kernel

private theorem block506823 : blockSum term 506823 614 1990146 := by unfold blockSum; decide +kernel

private theorem block507437 : blockSum term 507437 614 1939904 := by unfold blockSum; decide +kernel

private theorem block508051 : blockSum term 508051 614 2019397 := by unfold blockSum; decide +kernel

private theorem block508665 : blockSum term 508665 615 1712684 := by unfold blockSum; decide +kernel

private theorem block509280 : blockSum term 509280 614 2177032 := by unfold blockSum; decide +kernel

private theorem block509894 : blockSum term 509894 614 2042353 := by unfold blockSum; decide +kernel

private theorem block510508 : blockSum term 510508 614 1781203 := by unfold blockSum; decide +kernel

private theorem block511122 : blockSum term 511122 614 2240400 := by unfold blockSum; decide +kernel

private theorem block511736 : blockSum term 511736 614 1559082 := by unfold blockSum; decide +kernel

private theorem block512350 : blockSum term 512350 614 2057876 := by unfold blockSum; decide +kernel

private theorem block512964 : blockSum term 512964 614 2093152 := by unfold blockSum; decide +kernel

private theorem block513578 : blockSum term 513578 614 2001957 := by unfold blockSum; decide +kernel

private theorem block514192 : blockSum term 514192 614 1994813 := by unfold blockSum; decide +kernel

private theorem block514806 : blockSum term 514806 614 1615739 := by unfold blockSum; decide +kernel

private theorem block515420 : blockSum term 515420 614 1817156 := by unfold blockSum; decide +kernel

private theorem block516034 : blockSum term 516034 614 2222083 := by unfold blockSum; decide +kernel

private theorem block516648 : blockSum term 516648 614 2132063 := by unfold blockSum; decide +kernel

private theorem block517262 : blockSum term 517262 614 2043243 := by unfold blockSum; decide +kernel

private theorem block517876 : blockSum term 517876 614 1995689 := by unfold blockSum; decide +kernel

private theorem block518490 : blockSum term 518490 615 1826355 := by unfold blockSum; decide +kernel

private theorem block519105 : blockSum term 519105 614 1981749 := by unfold blockSum; decide +kernel

private theorem block519719 : blockSum term 519719 614 1692872 := by unfold blockSum; decide +kernel

private theorem block520333 : blockSum term 520333 614 1888285 := by unfold blockSum; decide +kernel

private theorem block520947 : blockSum term 520947 614 2161743 := by unfold blockSum; decide +kernel

private theorem block521561 : blockSum term 521561 614 1874784 := by unfold blockSum; decide +kernel

private theorem block522175 : blockSum term 522175 614 1987439 := by unfold blockSum; decide +kernel

private theorem block522789 : blockSum term 522789 614 1466269 := by unfold blockSum; decide +kernel

private theorem block523403 : blockSum term 523403 614 1896102 := by unfold blockSum; decide +kernel

private theorem block524017 : blockSum term 524017 614 1771505 := by unfold blockSum; decide +kernel

private theorem block524631 : blockSum term 524631 614 1961015 := by unfold blockSum; decide +kernel

private theorem block525245 : blockSum term 525245 614 1876325 := by unfold blockSum; decide +kernel

private theorem block525859 : blockSum term 525859 614 1986524 := by unfold blockSum; decide +kernel

private theorem block526473 : blockSum term 526473 614 2018234 := by unfold blockSum; decide +kernel

private theorem block527087 : blockSum term 527087 614 1701966 := by unfold blockSum; decide +kernel

private theorem block527701 : blockSum term 527701 614 1696182 := by unfold blockSum; decide +kernel

private theorem block528315 : blockSum term 528315 615 1652248 := by unfold blockSum; decide +kernel

private theorem block528930 : blockSum term 528930 614 1838057 := by unfold blockSum; decide +kernel

private theorem block529544 : blockSum term 529544 614 1755262 := by unfold blockSum; decide +kernel

private theorem block530158 : blockSum term 530158 614 1977028 := by unfold blockSum; decide +kernel

private theorem block530772 : blockSum term 530772 614 1742903 := by unfold blockSum; decide +kernel

private theorem block531386 : blockSum term 531386 614 1472177 := by unfold blockSum; decide +kernel

private theorem block532000 : blockSum term 532000 614 1843460 := by unfold blockSum; decide +kernel

private theorem block532614 : blockSum term 532614 614 1836964 := by unfold blockSum; decide +kernel

private theorem block533228 : blockSum term 533228 614 1531465 := by unfold blockSum; decide +kernel

private theorem block533842 : blockSum term 533842 614 1824237 := by unfold blockSum; decide +kernel

private theorem block534456 : blockSum term 534456 614 1558188 := by unfold blockSum; decide +kernel

private theorem block535070 : blockSum term 535070 614 1589797 := by unfold blockSum; decide +kernel

private theorem block535684 : blockSum term 535684 614 1841847 := by unfold blockSum; decide +kernel

private theorem block536298 : blockSum term 536298 614 1871907 := by unfold blockSum; decide +kernel

private theorem block536912 : blockSum term 536912 614 1609571 := by unfold blockSum; decide +kernel

private theorem block537526 : blockSum term 537526 614 1566815 := by unfold blockSum; decide +kernel

private theorem block538140 : blockSum term 538140 615 1779482 := by unfold blockSum; decide +kernel

private theorem block538755 : blockSum term 538755 614 1809141 := by unfold blockSum; decide +kernel

private theorem block539369 : blockSum term 539369 614 1370064 := by unfold blockSum; decide +kernel

private theorem block539983 : blockSum term 539983 614 1652630 := by unfold blockSum; decide +kernel

private theorem block540597 : blockSum term 540597 614 1503810 := by unfold blockSum; decide +kernel

private theorem block541211 : blockSum term 541211 614 1819011 := by unfold blockSum; decide +kernel

private theorem block541825 : blockSum term 541825 614 1599190 := by unfold blockSum; decide +kernel

private theorem block542439 : blockSum term 542439 614 1699690 := by unfold blockSum; decide +kernel

private theorem block543053 : blockSum term 543053 615 1728647 := by unfold blockSum; decide +kernel

private theorem block543668 : blockSum term 543668 614 1792035 := by unfold blockSum; decide +kernel

private theorem block544282 : blockSum term 544282 614 1329834 := by unfold blockSum; decide +kernel

private theorem block544896 : blockSum term 544896 614 1395330 := by unfold blockSum; decide +kernel

private theorem block545510 : blockSum term 545510 614 1703144 := by unfold blockSum; decide +kernel

private theorem block546124 : blockSum term 546124 614 1592874 := by unfold blockSum; decide +kernel

private theorem block546738 : blockSum term 546738 614 1276577 := by unfold blockSum; decide +kernel

private theorem block547352 : blockSum term 547352 614 1822115 := by unfold blockSum; decide +kernel

private theorem block547966 : blockSum term 547966 615 1575065 := by unfold blockSum; decide +kernel

private theorem block548581 : blockSum term 548581 614 1705472 := by unfold blockSum; decide +kernel

private theorem block549195 : blockSum term 549195 614 1631039 := by unfold blockSum; decide +kernel

private theorem block549809 : blockSum term 549809 614 1388259 := by unfold blockSum; decide +kernel

private theorem block550423 : blockSum term 550423 614 1787309 := by unfold blockSum; decide +kernel

private theorem block551037 : blockSum term 551037 614 1410870 := by unfold blockSum; decide +kernel

private theorem block551651 : blockSum term 551651 614 1706488 := by unfold blockSum; decide +kernel

private theorem block552265 : blockSum term 552265 614 1399769 := by unfold blockSum; decide +kernel

private theorem block552879 : blockSum term 552879 614 1527699 := by unfold blockSum; decide +kernel

private theorem block553493 : blockSum term 553493 614 1620941 := by unfold blockSum; decide +kernel

private theorem block554107 : blockSum term 554107 614 1449600 := by unfold blockSum; decide +kernel

private theorem block554721 : blockSum term 554721 614 1608140 := by unfold blockSum; decide +kernel

private theorem block555335 : blockSum term 555335 614 1177102 := by unfold blockSum; decide +kernel

private theorem block555949 : blockSum term 555949 614 1465904 := by unfold blockSum; decide +kernel

private theorem block556563 : blockSum term 556563 614 1849285 := by unfold blockSum; decide +kernel

private theorem block557177 : blockSum term 557177 614 1421372 := by unfold blockSum; decide +kernel

private theorem block557791 : blockSum term 557791 615 1255368 := by unfold blockSum; decide +kernel

private theorem block558406 : blockSum term 558406 614 1539223 := by unfold blockSum; decide +kernel

private theorem block559020 : blockSum term 559020 614 1533117 := by unfold blockSum; decide +kernel

private theorem block559634 : blockSum term 559634 614 1781180 := by unfold blockSum; decide +kernel

private theorem block560248 : blockSum term 560248 614 1457308 := by unfold blockSum; decide +kernel

private theorem block560862 : blockSum term 560862 614 1420125 := by unfold blockSum; decide +kernel

private theorem block561476 : blockSum term 561476 614 1006063 := by unfold blockSum; decide +kernel

private theorem block562090 : blockSum term 562090 614 1722909 := by unfold blockSum; decide +kernel

private theorem block562704 : blockSum term 562704 615 1435162 := by unfold blockSum; decide +kernel

private theorem block563319 : blockSum term 563319 614 1243072 := by unfold blockSum; decide +kernel

private theorem block563933 : blockSum term 563933 614 1609517 := by unfold blockSum; decide +kernel

private theorem block564547 : blockSum term 564547 614 1171586 := by unfold blockSum; decide +kernel

private theorem block565161 : blockSum term 565161 614 1689350 := by unfold blockSum; decide +kernel

private theorem block565775 : blockSum term 565775 614 1192902 := by unfold blockSum; decide +kernel

private theorem block566389 : blockSum term 566389 614 1462876 := by unfold blockSum; decide +kernel

private theorem block567003 : blockSum term 567003 614 1183950 := by unfold blockSum; decide +kernel

private theorem block567617 : blockSum term 567617 615 1602319 := by unfold blockSum; decide +kernel

private theorem block568232 : blockSum term 568232 614 1174721 := by unfold blockSum; decide +kernel

private theorem block568846 : blockSum term 568846 614 1440272 := by unfold blockSum; decide +kernel

private theorem block569460 : blockSum term 569460 614 1553163 := by unfold blockSum; decide +kernel

private theorem block570074 : blockSum term 570074 614 1606175 := by unfold blockSum; decide +kernel

private theorem block570688 : blockSum term 570688 614 1333008 := by unfold blockSum; decide +kernel

private theorem block571302 : blockSum term 571302 614 1356538 := by unfold blockSum; decide +kernel

private theorem block571916 : blockSum term 571916 614 1380164 := by unfold blockSum; decide +kernel

private theorem block572530 : blockSum term 572530 614 1462343 := by unfold blockSum; decide +kernel

private theorem block573144 : blockSum term 573144 614 1252185 := by unfold blockSum; decide +kernel

private theorem block573758 : blockSum term 573758 614 1363240 := by unfold blockSum; decide +kernel

private theorem block574372 : blockSum term 574372 614 1270991 := by unfold blockSum; decide +kernel

private theorem block574986 : blockSum term 574986 614 1323222 := by unfold blockSum; decide +kernel

private theorem block575600 : blockSum term 575600 614 1403511 := by unfold blockSum; decide +kernel

private theorem block576214 : blockSum term 576214 614 1482773 := by unfold blockSum; decide +kernel

private theorem block576828 : blockSum term 576828 614 1164066 := by unfold blockSum; decide +kernel

private theorem block577442 : blockSum term 577442 615 1356897 := by unfold blockSum; decide +kernel

private theorem block578057 : blockSum term 578057 614 1322805 := by unfold blockSum; decide +kernel

private theorem block578671 : blockSum term 578671 614 1261300 := by unfold blockSum; decide +kernel

private theorem block579285 : blockSum term 579285 614 1395207 := by unfold blockSum; decide +kernel

private theorem block579899 : blockSum term 579899 614 1083944 := by unfold blockSum; decide +kernel

private theorem block580513 : blockSum term 580513 614 1356619 := by unfold blockSum; decide +kernel

private theorem block581127 : blockSum term 581127 614 1405686 := by unfold blockSum; decide +kernel

private theorem block581741 : blockSum term 581741 614 1234927 := by unfold blockSum; decide +kernel

private theorem block582355 : blockSum term 582355 615 1229630 := by unfold blockSum; decide +kernel

private theorem block582970 : blockSum term 582970 614 1360315 := by unfold blockSum; decide +kernel

private theorem block583584 : blockSum term 583584 614 1164828 := by unfold blockSum; decide +kernel

private theorem block584198 : blockSum term 584198 614 1213197 := by unfold blockSum; decide +kernel

private theorem block584812 : blockSum term 584812 614 1261966 := by unfold blockSum; decide +kernel

private theorem block585426 : blockSum term 585426 614 1363243 := by unfold blockSum; decide +kernel

private theorem block586040 : blockSum term 586040 614 1277316 := by unfold blockSum; decide +kernel

private theorem block586654 : blockSum term 586654 614 1377594 := by unfold blockSum; decide +kernel

private theorem block587268 : blockSum term 587268 615 1371533 := by unfold blockSum; decide +kernel

private theorem block587883 : blockSum term 587883 614 1286616 := by unfold blockSum; decide +kernel

private theorem block588497 : blockSum term 588497 614 1071683 := by unfold blockSum; decide +kernel

private theorem block589111 : blockSum term 589111 614 1145113 := by unfold blockSum; decide +kernel

private theorem block589725 : blockSum term 589725 614 1191291 := by unfold blockSum; decide +kernel

private theorem block590339 : blockSum term 590339 614 1031362 := by unfold blockSum; decide +kernel

private theorem block590953 : blockSum term 590953 614 1078416 := by unfold blockSum; decide +kernel

private theorem block591567 : blockSum term 591567 614 1073744 := by unfold blockSum; decide +kernel

private theorem block592181 : blockSum term 592181 614 1323266 := by unfold blockSum; decide +kernel

private theorem block592795 : blockSum term 592795 614 1291640 := by unfold blockSum; decide +kernel

private theorem block593409 : blockSum term 593409 614 1033934 := by unfold blockSum; decide +kernel

private theorem block594023 : blockSum term 594023 614 1229589 := by unfold blockSum; decide +kernel

private theorem block594637 : blockSum term 594637 614 1323553 := by unfold blockSum; decide +kernel

private theorem block595251 : blockSum term 595251 614 1019332 := by unfold blockSum; decide +kernel

private theorem block595865 : blockSum term 595865 614 1163093 := by unfold blockSum; decide +kernel

private theorem block596479 : blockSum term 596479 614 1206967 := by unfold blockSum; decide +kernel

private theorem block597093 : blockSum term 597093 615 1200811 := by unfold blockSum; decide +kernel

private theorem block597708 : blockSum term 597708 614 975823 := by unfold blockSum; decide +kernel

private theorem block598322 : blockSum term 598322 614 1092966 := by unfold blockSum; decide +kernel

private theorem block598936 : blockSum term 598936 614 1063862 := by unfold blockSum; decide +kernel

private theorem block599550 : blockSum term 599550 614 1034931 := by unfold blockSum; decide +kernel

private theorem block600164 : blockSum term 600164 614 1173360 := by unfold blockSum; decide +kernel

private theorem block600778 : blockSum term 600778 614 1214662 := by unfold blockSum; decide +kernel

private theorem block601392 : blockSum term 601392 614 971724 := by unfold blockSum; decide +kernel

private theorem block602006 : blockSum term 602006 614 1202992 := by unfold blockSum; decide +kernel

private theorem block602620 : blockSum term 602620 614 1149977 := by unfold blockSum; decide +kernel

private theorem block603234 : blockSum term 603234 614 980684 := by unfold blockSum; decide +kernel

private theorem block603848 : blockSum term 603848 614 1115851 := by unfold blockSum; decide +kernel

private theorem block604462 : blockSum term 604462 614 1132997 := by unfold blockSum; decide +kernel

private theorem block605076 : blockSum term 605076 614 1058157 := by unfold blockSum; decide +kernel

private theorem block605690 : blockSum term 605690 614 984372 := by unfold blockSum; decide +kernel

private theorem block606304 : blockSum term 606304 614 979690 := by unfold blockSum; decide +kernel

private theorem block606918 : blockSum term 606918 615 1178856 := by unfold blockSum; decide +kernel

private theorem block607533 : blockSum term 607533 614 970296 := by unfold blockSum; decide +kernel

private theorem block608147 : blockSum term 608147 614 1078103 := by unfold blockSum; decide +kernel

private theorem block608761 : blockSum term 608761 614 1117098 := by unfold blockSum; decide +kernel

private theorem block609375 : blockSum term 609375 614 1044927 := by unfold blockSum; decide +kernel

private theorem block609989 : blockSum term 609989 614 884737 := by unfold blockSum; decide +kernel

private theorem block610603 : blockSum term 610603 614 1144020 := by unfold blockSum; decide +kernel

private theorem block611217 : blockSum term 611217 614 831512 := by unfold blockSum; decide +kernel

private theorem block611831 : blockSum term 611831 614 1218810 := by unfold blockSum; decide +kernel

private theorem block612445 : blockSum term 612445 614 887227 := by unfold blockSum; decide +kernel

private theorem block613059 : blockSum term 613059 614 1119554 := by unfold blockSum; decide +kernel

private theorem block613673 : blockSum term 613673 614 877902 := by unfold blockSum; decide +kernel

private theorem block614287 : blockSum term 614287 614 1001403 := by unfold blockSum; decide +kernel

private theorem block614901 : blockSum term 614901 614 953862 := by unfold blockSum; decide +kernel

private theorem block615515 : blockSum term 615515 614 949198 := by unfold blockSum; decide +kernel

private theorem block616129 : blockSum term 616129 614 1132845 := by unfold blockSum; decide +kernel

private theorem block616743 : blockSum term 616743 615 1084761 := by unfold blockSum; decide +kernel

private theorem block617358 : blockSum term 617358 614 1037698 := by unfold blockSum; decide +kernel

private theorem block617972 : blockSum term 617972 614 846205 := by unfold blockSum; decide +kernel

private theorem block618586 : blockSum term 618586 614 903351 := by unfold blockSum; decide +kernel

private theorem block619200 : blockSum term 619200 614 878308 := by unfold blockSum; decide +kernel

private theorem block619814 : blockSum term 619814 614 914150 := by unfold blockSum; decide +kernel

private theorem block620428 : blockSum term 620428 614 1010255 := by unfold blockSum; decide +kernel

private theorem block621042 : blockSum term 621042 614 823845 := by unfold blockSum; decide +kernel

private theorem block621656 : blockSum term 621656 615 939321 := by unfold blockSum; decide +kernel

private theorem block622271 : blockSum term 622271 614 854642 := by unfold blockSum; decide +kernel

private theorem block622885 : blockSum term 622885 614 830050 := by unfold blockSum; decide +kernel

private theorem block623499 : blockSum term 623499 614 963331 := by unfold blockSum; decide +kernel

private theorem block624113 : blockSum term 624113 614 958078 := by unfold blockSum; decide +kernel

private theorem block624727 : blockSum term 624727 614 874818 := by unfold blockSum; decide +kernel

private theorem block625341 : blockSum term 625341 614 811835 := by unfold blockSum; decide +kernel

private theorem block625955 : blockSum term 625955 614 692312 := by unfold blockSum; decide +kernel

private theorem block626569 : blockSum term 626569 615 975074 := by unfold blockSum; decide +kernel

private theorem block627184 : blockSum term 627184 614 836321 := by unfold blockSum; decide +kernel

private theorem block627798 : blockSum term 627798 614 812822 := by unfold blockSum; decide +kernel

private theorem block628412 : blockSum term 628412 614 826893 := by unfold blockSum; decide +kernel

private theorem block629026 : blockSum term 629026 614 728920 := by unfold blockSum; decide +kernel

private theorem block629640 : blockSum term 629640 614 911070 := by unfold blockSum; decide +kernel

private theorem block630254 : blockSum term 630254 614 739118 := by unfold blockSum; decide +kernel

private theorem block630868 : blockSum term 630868 614 826606 := by unfold blockSum; decide +kernel

private theorem block631482 : blockSum term 631482 614 967616 := by unfold blockSum; decide +kernel

private theorem block632096 : blockSum term 632096 614 889009 := by unfold blockSum; decide +kernel

private theorem block632710 : blockSum term 632710 614 757620 := by unfold blockSum; decide +kernel

private theorem block633324 : blockSum term 633324 614 789115 := by unfold blockSum; decide +kernel

private theorem block633938 : blockSum term 633938 614 890797 := by unfold blockSum; decide +kernel

private theorem block634552 : blockSum term 634552 614 814495 := by unfold blockSum; decide +kernel

private theorem block635166 : blockSum term 635166 614 862423 := by unfold blockSum; decide +kernel

private theorem block635780 : blockSum term 635780 614 857278 := by unfold blockSum; decide +kernel

private theorem block636394 : blockSum term 636394 615 799479 := by unfold blockSum; decide +kernel

private theorem block637009 : blockSum term 637009 614 794883 := by unfold blockSum; decide +kernel

private theorem block637623 : blockSum term 637623 614 721549 := by unfold blockSum; decide +kernel

private theorem block638237 : blockSum term 638237 614 563561 := by unfold blockSum; decide +kernel

private theorem block638851 : blockSum term 638851 614 695975 := by unfold blockSum; decide +kernel

private theorem block639465 : blockSum term 639465 614 843322 := by unfold blockSum; decide +kernel

private theorem block640079 : blockSum term 640079 614 753925 := by unfold blockSum; decide +kernel

private theorem block640693 : blockSum term 640693 614 716052 := by unfold blockSum; decide +kernel

private theorem block641307 : blockSum term 641307 615 760835 := by unfold blockSum; decide +kernel

private theorem block641922 : blockSum term 641922 614 673940 := by unfold blockSum; decide +kernel

private theorem block642536 : blockSum term 642536 614 734685 := by unfold blockSum; decide +kernel

private theorem block643150 : blockSum term 643150 614 681741 := by unfold blockSum; decide +kernel

private theorem block643764 : blockSum term 643764 614 773625 := by unfold blockSum; decide +kernel

private theorem block644378 : blockSum term 644378 614 832543 := by unfold blockSum; decide +kernel

private theorem block644992 : blockSum term 644992 614 731302 := by unfold blockSum; decide +kernel

private theorem block645606 : blockSum term 645606 614 742221 := by unfold blockSum; decide +kernel

private theorem block646220 : blockSum term 646220 615 627709 := by unfold blockSum; decide +kernel

private theorem block646835 : blockSum term 646835 614 810583 := by unfold blockSum; decide +kernel

private theorem block647449 : blockSum term 647449 614 789196 := by unfold blockSum; decide +kernel

private theorem block648063 : blockSum term 648063 614 676111 := by unfold blockSum; decide +kernel

private theorem block648677 : blockSum term 648677 614 671314 := by unfold blockSum; decide +kernel

private theorem block649291 : blockSum term 649291 614 848409 := by unfold blockSum; decide +kernel

private theorem block649905 : blockSum term 649905 614 511668 := by unfold blockSum; decide +kernel

private theorem block650519 : blockSum term 650519 614 643123 := by unfold blockSum; decide +kernel

private theorem block651133 : blockSum term 651133 614 653725 := by unfold blockSum; decide +kernel

private theorem block651747 : blockSum term 651747 614 693285 := by unfold blockSum; decide +kernel

private theorem block652361 : blockSum term 652361 614 805382 := by unfold blockSum; decide +kernel

private theorem block652975 : blockSum term 652975 614 537810 := by unfold blockSum; decide +kernel

private theorem block653589 : blockSum term 653589 614 765122 := by unfold blockSum; decide +kernel

private theorem block654203 : blockSum term 654203 614 673201 := by unfold blockSum; decide +kernel

private theorem block654817 : blockSum term 654817 614 668479 := by unfold blockSum; decide +kernel

private theorem block655431 : blockSum term 655431 614 578830 := by unfold blockSum; decide +kernel

private theorem block656045 : blockSum term 656045 615 602824 := by unfold blockSum; decide +kernel

private theorem block656660 : blockSum term 656660 614 626669 := by unfold blockSum; decide +kernel

private theorem block657274 : blockSum term 657274 614 594370 := by unfold blockSum; decide +kernel

private theorem block657888 : blockSum term 657888 614 658351 := by unfold blockSum; decide +kernel

private theorem block658502 : blockSum term 658502 614 639729 := by unfold blockSum; decide +kernel

private theorem block659116 : blockSum term 659116 614 620967 := by unfold blockSum; decide +kernel

private theorem block659730 : blockSum term 659730 614 643162 := by unfold blockSum; decide +kernel

private theorem block660344 : blockSum term 660344 614 691167 := by unfold blockSum; decide +kernel

private theorem block660958 : blockSum term 660958 615 580300 := by unfold blockSum; decide +kernel

private theorem block661573 : blockSum term 661573 614 536625 := by unfold blockSum; decide +kernel

private theorem block662187 : blockSum term 662187 614 597500 := by unfold blockSum; decide +kernel

private theorem block662801 : blockSum term 662801 614 580189 := by unfold blockSum; decide +kernel

private theorem block663415 : blockSum term 663415 614 626598 := by unfold blockSum; decide +kernel

private theorem block664029 : blockSum term 664029 614 621389 := by unfold blockSum; decide +kernel

private theorem block664643 : blockSum term 664643 614 641544 := by unfold blockSum; decide +kernel

private theorem block665257 : blockSum term 665257 614 549162 := by unfold blockSum; decide +kernel

private theorem block665871 : blockSum term 665871 615 520249 := by unfold blockSum; decide +kernel

private theorem block666486 : blockSum term 666486 614 540537 := by unfold blockSum; decide +kernel

private theorem block667100 : blockSum term 667100 614 584387 := by unfold blockSum; decide +kernel

private theorem block667714 : blockSum term 667714 614 495025 := by unfold blockSum; decide +kernel

private theorem block668328 : blockSum term 668328 614 490728 := by unfold blockSum; decide +kernel

private theorem block668942 : blockSum term 668942 614 522570 := by unfold blockSum; decide +kernel

private theorem block669556 : blockSum term 669556 614 541802 := by unfold blockSum; decide +kernel

private theorem block670170 : blockSum term 670170 614 583951 := by unfold blockSum; decide +kernel

private theorem block670784 : blockSum term 670784 614 520943 := by unfold blockSum; decide +kernel

private theorem block671398 : blockSum term 671398 614 516388 := by unfold blockSum; decide +kernel

private theorem block672012 : blockSum term 672012 614 512100 := by unfold blockSum; decide +kernel

private theorem block672626 : blockSum term 672626 614 552047 := by unfold blockSum; decide +kernel

private theorem block673240 : blockSum term 673240 614 569304 := by unfold blockSum; decide +kernel

private theorem block673854 : blockSum term 673854 614 442207 := by unfold blockSum; decide +kernel

private theorem block674468 : blockSum term 674468 614 493040 := by unfold blockSum; decide +kernel

private theorem block675082 : blockSum term 675082 614 520835 := by unfold blockSum; decide +kernel

private theorem block675696 : blockSum term 675696 615 505179 := by unfold blockSum; decide +kernel

private theorem block676311 : blockSum term 676311 614 425917 := by unfold blockSum; decide +kernel

private theorem block676925 : blockSum term 676925 614 485364 := by unfold blockSum; decide +kernel

private theorem block677539 : blockSum term 677539 614 365727 := by unfold blockSum; decide +kernel

private theorem block678153 : blockSum term 678153 614 579819 := by unfold blockSum; decide +kernel

private theorem block678767 : blockSum term 678767 614 481724 := by unfold blockSum; decide +kernel

private theorem block679381 : blockSum term 679381 614 537477 := by unfold blockSum; decide +kernel

private theorem block679995 : blockSum term 679995 614 501932 := by unfold blockSum; decide +kernel

private theorem block680609 : blockSum term 680609 615 427342 := by unfold blockSum; decide +kernel

private theorem block681224 : blockSum term 681224 614 472441 := by unfold blockSum; decide +kernel

private theorem block681838 : blockSum term 681838 614 467412 := by unfold blockSum; decide +kernel

private theorem block682452 : blockSum term 682452 614 337678 := by unfold blockSum; decide +kernel

private theorem block683066 : blockSum term 683066 614 391841 := by unfold blockSum; decide +kernel

private theorem block683680 : blockSum term 683680 614 501239 := by unfold blockSum; decide +kernel

private theorem block684294 : blockSum term 684294 614 430201 := by unfold blockSum; decide +kernel

private theorem block684908 : blockSum term 684908 614 443929 := by unfold blockSum; decide +kernel

private theorem block685522 : blockSum term 685522 615 420574 := by unfold blockSum; decide +kernel

private theorem block686137 : blockSum term 686137 614 361970 := by unfold blockSum; decide +kernel

private theorem block686751 : blockSum term 686751 614 465437 := by unfold blockSum; decide +kernel

private theorem block687365 : blockSum term 687365 614 442655 := by unfold blockSum; decide +kernel

private theorem block687979 : blockSum term 687979 614 376569 := by unfold blockSum; decide +kernel

private theorem block688593 : blockSum term 688593 614 398528 := by unfold blockSum; decide +kernel

private theorem block689207 : blockSum term 689207 614 385207 := by unfold blockSum; decide +kernel

private theorem block689821 : blockSum term 689821 614 380619 := by unfold blockSum; decide +kernel

private theorem block690435 : blockSum term 690435 614 301129 := by unfold blockSum; decide +kernel

private theorem block691049 : blockSum term 691049 614 364045 := by unfold blockSum; decide +kernel

private theorem block691663 : blockSum term 691663 614 425267 := by unfold blockSum; decide +kernel

private theorem block692277 : blockSum term 692277 614 396012 := by unfold blockSum; decide +kernel

private theorem block692891 : blockSum term 692891 614 343227 := by unfold blockSum; decide +kernel

private theorem block693505 : blockSum term 693505 614 378088 := by unfold blockSum; decide +kernel

private theorem block694119 : blockSum term 694119 614 373105 := by unfold blockSum; decide +kernel

private theorem block694733 : blockSum term 694733 614 360931 := by unfold blockSum; decide +kernel

private theorem block695347 : blockSum term 695347 615 363957 := by unfold blockSum; decide +kernel

private theorem block695962 : blockSum term 695962 614 314276 := by unfold blockSum; decide +kernel

private theorem block696576 : blockSum term 696576 614 361764 := by unfold blockSum; decide +kernel

private theorem block697190 : blockSum term 697190 614 349525 := by unfold blockSum; decide +kernel

private theorem block697804 : blockSum term 697804 614 301620 := by unfold blockSum; decide +kernel

private theorem block698418 : blockSum term 698418 614 255608 := by unfold blockSum; decide +kernel

private theorem block699032 : blockSum term 699032 614 356860 := by unfold blockSum; decide +kernel

private theorem block699646 : blockSum term 699646 614 269039 := by unfold blockSum; decide +kernel

private theorem block700260 : blockSum term 700260 615 306377 := by unfold blockSum; decide +kernel

private theorem block700875 : blockSum term 700875 614 301771 := by unfold blockSum; decide +kernel

private theorem block701489 : blockSum term 701489 614 277970 := by unfold blockSum; decide +kernel

private theorem block702103 : blockSum term 702103 614 351691 := by unfold blockSum; decide +kernel

private theorem block702717 : blockSum term 702717 614 294936 := by unfold blockSum; decide +kernel

private theorem block703331 : blockSum term 703331 614 265440 := by unfold blockSum; decide +kernel

private theorem block703945 : blockSum term 703945 614 317339 := by unfold blockSum; decide +kernel

private theorem block704559 : blockSum term 704559 614 348385 := by unfold blockSum; decide +kernel

private theorem block705173 : blockSum term 705173 615 216566 := by unfold blockSum; decide +kernel

private theorem block705788 : blockSum term 705788 614 296353 := by unfold blockSum; decide +kernel

private theorem block706402 : blockSum term 706402 614 279737 := by unfold blockSum; decide +kernel

private theorem block707016 : blockSum term 707016 614 212192 := by unfold blockSum; decide +kernel

private theorem block707630 : blockSum term 707630 614 332412 := by unfold blockSum; decide +kernel

private theorem block708244 : blockSum term 708244 614 226964 := by unfold blockSum; decide +kernel

private theorem block708858 : blockSum term 708858 614 250215 := by unfold blockSum; decide +kernel

private theorem block709472 : blockSum term 709472 614 267257 := by unfold blockSum; decide +kernel

private theorem block710086 : blockSum term 710086 614 246259 := by unfold blockSum; decide +kernel

private theorem block710700 : blockSum term 710700 614 241597 := by unfold blockSum; decide +kernel

private theorem block711314 : blockSum term 711314 614 237147 := by unfold blockSum; decide +kernel

private theorem block711928 : blockSum term 711928 614 222852 := by unfold blockSum; decide +kernel

private theorem block712542 : blockSum term 712542 614 208998 := by unfold blockSum; decide +kernel

private theorem block713156 : blockSum term 713156 614 223974 := by unfold blockSum; decide +kernel

private theorem block713770 : blockSum term 713770 614 177532 := by unfold blockSum; decide +kernel

private theorem block714384 : blockSum term 714384 614 205867 := by unfold blockSum; decide +kernel

private theorem block714998 : blockSum term 714998 615 206358 := by unfold blockSum; decide +kernel

private theorem block715613 : blockSum term 715613 614 210968 := by unfold blockSum; decide +kernel

private theorem block716227 : blockSum term 716227 614 197750 := by unfold blockSum; decide +kernel

private theorem block716841 : blockSum term 716841 614 176793 := by unfold blockSum; decide +kernel

private theorem block717455 : blockSum term 717455 614 160586 := by unfold blockSum; decide +kernel

private theorem block718069 : blockSum term 718069 614 169183 := by unfold blockSum; decide +kernel

private theorem block718683 : blockSum term 718683 614 177174 := by unfold blockSum; decide +kernel

private theorem block719297 : blockSum term 719297 614 165333 := by unfold blockSum; decide +kernel

private theorem block719911 : blockSum term 719911 615 176353 := by unfold blockSum; decide +kernel

private theorem block720526 : blockSum term 720526 614 186132 := by unfold blockSum; decide +kernel

private theorem block721140 : blockSum term 721140 614 177767 := by unfold blockSum; decide +kernel

private theorem block721754 : blockSum term 721754 614 155428 := by unfold blockSum; decide +kernel

private theorem block722368 : blockSum term 722368 614 137975 := by unfold blockSum; decide +kernel

private theorem block722982 : blockSum term 722982 614 182999 := by unfold blockSum; decide +kernel

private theorem block723596 : blockSum term 723596 614 136431 := by unfold blockSum; decide +kernel

private theorem block724210 : blockSum term 724210 614 156753 := by unfold blockSum; decide +kernel

private theorem block724824 : blockSum term 724824 615 130931 := by unfold blockSum; decide +kernel

private theorem block725439 : blockSum term 725439 614 118022 := by unfold blockSum; decide +kernel

private theorem block726053 : blockSum term 726053 614 133885 := by unfold blockSum; decide +kernel

private theorem block726667 : blockSum term 726667 614 129070 := by unfold blockSum; decide +kernel

private theorem block727281 : blockSum term 727281 614 119257 := by unfold blockSum; decide +kernel

private theorem block727895 : blockSum term 727895 614 87804 := by unfold blockSum; decide +kernel

private theorem block728509 : blockSum term 728509 614 126014 := by unfold blockSum; decide +kernel

private theorem block729123 : blockSum term 729123 614 113452 := by unfold blockSum; decide +kernel

private theorem block729737 : blockSum term 729737 614 86845 := by unfold blockSum; decide +kernel

private theorem block730351 : blockSum term 730351 614 98026 := by unfold blockSum; decide +kernel

private theorem block730965 : blockSum term 730965 614 87691 := by unfold blockSum; decide +kernel

private theorem block731579 : blockSum term 731579 614 99073 := by unfold blockSum; decide +kernel

private theorem block732193 : blockSum term 732193 614 77649 := by unfold blockSum; decide +kernel

private theorem block732807 : blockSum term 732807 614 86009 := by unfold blockSum; decide +kernel

private theorem block733421 : blockSum term 733421 614 73365 := by unfold blockSum; decide +kernel

private theorem block734035 : blockSum term 734035 614 66570 := by unfold blockSum; decide +kernel

private theorem block734649 : blockSum term 734649 615 79146 := by unfold blockSum; decide +kernel

private theorem block735264 : blockSum term 735264 614 64245 := by unfold blockSum; decide +kernel

private theorem block735878 : blockSum term 735878 614 63585 := by unfold blockSum; decide +kernel

private theorem block736492 : blockSum term 736492 614 44374 := by unfold blockSum; decide +kernel

private theorem block737106 : blockSum term 737106 614 54816 := by unfold blockSum; decide +kernel

private theorem block737720 : blockSum term 737720 614 44220 := by unfold blockSum; decide +kernel

private theorem block738334 : blockSum term 738334 614 41113 := by unfold blockSum; decide +kernel

private theorem block738948 : blockSum term 738948 614 45773 := by unfold blockSum; decide +kernel

private theorem block739562 : blockSum term 739562 615 32497 := by unfold blockSum; decide +kernel

private theorem block740177 : blockSum term 740177 614 27396 := by unfold blockSum; decide +kernel

private theorem block740791 : blockSum term 740791 614 23220 := by unfold blockSum; decide +kernel

private theorem block741405 : blockSum term 741405 614 21324 := by unfold blockSum; decide +kernel

private theorem block742019 : blockSum term 742019 614 17645 := by unfold blockSum; decide +kernel

private theorem block742633 : blockSum term 742633 614 13372 := by unfold blockSum; decide +kernel

private theorem block743247 : blockSum term 743247 614 7863 := by unfold blockSum; decide +kernel

private theorem block743861 : blockSum term 743861 614 4681 := by unfold blockSum; decide +kernel

private theorem block744475 : blockSum term 744475 615 1695 := by unfold blockSum; decide +kernel

set_option maxRecDepth 16000 in
private theorem after_cut : blockSum term 116264 628826 4397030859 := (join_sums term (lo:=116264) (a:=314413) (b:=314413) (join_sums term (lo:=116264) (a:=157206) (b:=157207) (join_sums term (lo:=116264) (a:=78603) (b:=78603) (join_sums term (lo:=116264) (a:=39301) (b:=39302) (join_sums term (lo:=116264) (a:=19650) (b:=19651) (join_sums term (lo:=116264) (a:=9825) (b:=9825) (join_sums term (lo:=116264) (a:=4912) (b:=4913) (join_sums term (lo:=116264) (a:=2456) (b:=2456) (join_sums term (lo:=116264) (a:=1228) (b:=1228) (join_sums term (lo:=116264) (a:=614) (b:=614) block116264 block116878) (join_sums term (lo:=117492) (a:=614) (b:=614) block117492 block118106)) (join_sums term (lo:=118720) (a:=1228) (b:=1228) (join_sums term (lo:=118720) (a:=614) (b:=614) block118720 block119334) (join_sums term (lo:=119948) (a:=614) (b:=614) block119948 block120562))) (join_sums term (lo:=121176) (a:=2456) (b:=2457) (join_sums term (lo:=121176) (a:=1228) (b:=1228) (join_sums term (lo:=121176) (a:=614) (b:=614) block121176 block121790) (join_sums term (lo:=122404) (a:=614) (b:=614) block122404 block123018)) (join_sums term (lo:=123632) (a:=1228) (b:=1229) (join_sums term (lo:=123632) (a:=614) (b:=614) block123632 block124246) (join_sums term (lo:=124860) (a:=614) (b:=615) block124860 block125474)))) (join_sums term (lo:=126089) (a:=4912) (b:=4913) (join_sums term (lo:=126089) (a:=2456) (b:=2456) (join_sums term (lo:=126089) (a:=1228) (b:=1228) (join_sums term (lo:=126089) (a:=614) (b:=614) block126089 block126703) (join_sums term (lo:=127317) (a:=614) (b:=614) block127317 block127931)) (join_sums term (lo:=128545) (a:=1228) (b:=1228) (join_sums term (lo:=128545) (a:=614) (b:=614) block128545 block129159) (join_sums term (lo:=129773) (a:=614) (b:=614) block129773 block130387))) (join_sums term (lo:=131001) (a:=2456) (b:=2457) (join_sums term (lo:=131001) (a:=1228) (b:=1228) (join_sums term (lo:=131001) (a:=614) (b:=614) block131001 block131615) (join_sums term (lo:=132229) (a:=614) (b:=614) block132229 block132843)) (join_sums term (lo:=133457) (a:=1228) (b:=1229) (join_sums term (lo:=133457) (a:=614) (b:=614) block133457 block134071) (join_sums term (lo:=134685) (a:=614) (b:=615) block134685 block135299))))) (join_sums term (lo:=135914) (a:=9825) (b:=9826) (join_sums term (lo:=135914) (a:=4912) (b:=4913) (join_sums term (lo:=135914) (a:=2456) (b:=2456) (join_sums term (lo:=135914) (a:=1228) (b:=1228) (join_sums term (lo:=135914) (a:=614) (b:=614) block135914 block136528) (join_sums term (lo:=137142) (a:=614) (b:=614) block137142 block137756)) (join_sums term (lo:=138370) (a:=1228) (b:=1228) (join_sums term (lo:=138370) (a:=614) (b:=614) block138370 block138984) (join_sums term (lo:=139598) (a:=614) (b:=614) block139598 block140212))) (join_sums term (lo:=140826) (a:=2456) (b:=2457) (join_sums term (lo:=140826) (a:=1228) (b:=1228) (join_sums term (lo:=140826) (a:=614) (b:=614) block140826 block141440) (join_sums term (lo:=142054) (a:=614) (b:=614) block142054 block142668)) (join_sums term (lo:=143282) (a:=1228) (b:=1229) (join_sums term (lo:=143282) (a:=614) (b:=614) block143282 block143896) (join_sums term (lo:=144510) (a:=614) (b:=615) block144510 block145124)))) (join_sums term (lo:=145739) (a:=4913) (b:=4913) (join_sums term (lo:=145739) (a:=2456) (b:=2457) (join_sums term (lo:=145739) (a:=1228) (b:=1228) (join_sums term (lo:=145739) (a:=614) (b:=614) block145739 block146353) (join_sums term (lo:=146967) (a:=614) (b:=614) block146967 block147581)) (join_sums term (lo:=148195) (a:=1228) (b:=1229) (join_sums term (lo:=148195) (a:=614) (b:=614) block148195 block148809) (join_sums term (lo:=149423) (a:=614) (b:=615) block149423 block150037))) (join_sums term (lo:=150652) (a:=2456) (b:=2457) (join_sums term (lo:=150652) (a:=1228) (b:=1228) (join_sums term (lo:=150652) (a:=614) (b:=614) block150652 block151266) (join_sums term (lo:=151880) (a:=614) (b:=614) block151880 block152494)) (join_sums term (lo:=153108) (a:=1228) (b:=1229) (join_sums term (lo:=153108) (a:=614) (b:=614) block153108 block153722) (join_sums term (lo:=154336) (a:=614) (b:=615) block154336 block154950)))))) (join_sums term (lo:=155565) (a:=19651) (b:=19651) (join_sums term (lo:=155565) (a:=9825) (b:=9826) (join_sums term (lo:=155565) (a:=4912) (b:=4913) (join_sums term (lo:=155565) (a:=2456) (b:=2456) (join_sums term (lo:=155565) (a:=1228) (b:=1228) (join_sums term (lo:=155565) (a:=614) (b:=614) block155565 block156179) (join_sums term (lo:=156793) (a:=614) (b:=614) block156793 block157407)) (join_sums term (lo:=158021) (a:=1228) (b:=1228) (join_sums term (lo:=158021) (a:=614) (b:=614) block158021 block158635) (join_sums term (lo:=159249) (a:=614) (b:=614) block159249 block159863))) (join_sums term (lo:=160477) (a:=2456) (b:=2457) (join_sums term (lo:=160477) (a:=1228) (b:=1228) (join_sums term (lo:=160477) (a:=614) (b:=614) block160477 block161091) (join_sums term (lo:=161705) (a:=614) (b:=614) block161705 block162319)) (join_sums term (lo:=162933) (a:=1228) (b:=1229) (join_sums term (lo:=162933) (a:=614) (b:=614) block162933 block163547) (join_sums term (lo:=164161) (a:=614) (b:=615) block164161 block164775)))) (join_sums term (lo:=165390) (a:=4913) (b:=4913) (join_sums term (lo:=165390) (a:=2456) (b:=2457) (join_sums term (lo:=165390) (a:=1228) (b:=1228) (join_sums term (lo:=165390) (a:=614) (b:=614) block165390 block166004) (join_sums term (lo:=166618) (a:=614) (b:=614) block166618 block167232)) (join_sums term (lo:=167846) (a:=1228) (b:=1229) (join_sums term (lo:=167846) (a:=614) (b:=614) block167846 block168460) (join_sums term (lo:=169074) (a:=614) (b:=615) block169074 block169688))) (join_sums term (lo:=170303) (a:=2456) (b:=2457) (join_sums term (lo:=170303) (a:=1228) (b:=1228) (join_sums term (lo:=170303) (a:=614) (b:=614) block170303 block170917) (join_sums term (lo:=171531) (a:=614) (b:=614) block171531 block172145)) (join_sums term (lo:=172759) (a:=1228) (b:=1229) (join_sums term (lo:=172759) (a:=614) (b:=614) block172759 block173373) (join_sums term (lo:=173987) (a:=614) (b:=615) block173987 block174601))))) (join_sums term (lo:=175216) (a:=9825) (b:=9826) (join_sums term (lo:=175216) (a:=4912) (b:=4913) (join_sums term (lo:=175216) (a:=2456) (b:=2456) (join_sums term (lo:=175216) (a:=1228) (b:=1228) (join_sums term (lo:=175216) (a:=614) (b:=614) block175216 block175830) (join_sums term (lo:=176444) (a:=614) (b:=614) block176444 block177058)) (join_sums term (lo:=177672) (a:=1228) (b:=1228) (join_sums term (lo:=177672) (a:=614) (b:=614) block177672 block178286) (join_sums term (lo:=178900) (a:=614) (b:=614) block178900 block179514))) (join_sums term (lo:=180128) (a:=2456) (b:=2457) (join_sums term (lo:=180128) (a:=1228) (b:=1228) (join_sums term (lo:=180128) (a:=614) (b:=614) block180128 block180742) (join_sums term (lo:=181356) (a:=614) (b:=614) block181356 block181970)) (join_sums term (lo:=182584) (a:=1228) (b:=1229) (join_sums term (lo:=182584) (a:=614) (b:=614) block182584 block183198) (join_sums term (lo:=183812) (a:=614) (b:=615) block183812 block184426)))) (join_sums term (lo:=185041) (a:=4913) (b:=4913) (join_sums term (lo:=185041) (a:=2456) (b:=2457) (join_sums term (lo:=185041) (a:=1228) (b:=1228) (join_sums term (lo:=185041) (a:=614) (b:=614) block185041 block185655) (join_sums term (lo:=186269) (a:=614) (b:=614) block186269 block186883)) (join_sums term (lo:=187497) (a:=1228) (b:=1229) (join_sums term (lo:=187497) (a:=614) (b:=614) block187497 block188111) (join_sums term (lo:=188725) (a:=614) (b:=615) block188725 block189339))) (join_sums term (lo:=189954) (a:=2456) (b:=2457) (join_sums term (lo:=189954) (a:=1228) (b:=1228) (join_sums term (lo:=189954) (a:=614) (b:=614) block189954 block190568) (join_sums term (lo:=191182) (a:=614) (b:=614) block191182 block191796)) (join_sums term (lo:=192410) (a:=1228) (b:=1229) (join_sums term (lo:=192410) (a:=614) (b:=614) block192410 block193024) (join_sums term (lo:=193638) (a:=614) (b:=615) block193638 block194252))))))) (join_sums term (lo:=194867) (a:=39301) (b:=39302) (join_sums term (lo:=194867) (a:=19650) (b:=19651) (join_sums term (lo:=194867) (a:=9825) (b:=9825) (join_sums term (lo:=194867) (a:=4912) (b:=4913) (join_sums term (lo:=194867) (a:=2456) (b:=2456) (join_sums term (lo:=194867) (a:=1228) (b:=1228) (join_sums term (lo:=194867) (a:=614) (b:=614) block194867 block195481) (join_sums term (lo:=196095) (a:=614) (b:=614) block196095 block196709)) (join_sums term (lo:=197323) (a:=1228) (b:=1228) (join_sums term (lo:=197323) (a:=614) (b:=614) block197323 block197937) (join_sums term (lo:=198551) (a:=614) (b:=614) block198551 block199165))) (join_sums term (lo:=199779) (a:=2456) (b:=2457) (join_sums term (lo:=199779) (a:=1228) (b:=1228) (join_sums term (lo:=199779) (a:=614) (b:=614) block199779 block200393) (join_sums term (lo:=201007) (a:=614) (b:=614) block201007 block201621)) (join_sums term (lo:=202235) (a:=1228) (b:=1229) (join_sums term (lo:=202235) (a:=614) (b:=614) block202235 block202849) (join_sums term (lo:=203463) (a:=614) (b:=615) block203463 block204077)))) (join_sums term (lo:=204692) (a:=4912) (b:=4913) (join_sums term (lo:=204692) (a:=2456) (b:=2456) (join_sums term (lo:=204692) (a:=1228) (b:=1228) (join_sums term (lo:=204692) (a:=614) (b:=614) block204692 block205306) (join_sums term (lo:=205920) (a:=614) (b:=614) block205920 block206534)) (join_sums term (lo:=207148) (a:=1228) (b:=1228) (join_sums term (lo:=207148) (a:=614) (b:=614) block207148 block207762) (join_sums term (lo:=208376) (a:=614) (b:=614) block208376 block208990))) (join_sums term (lo:=209604) (a:=2456) (b:=2457) (join_sums term (lo:=209604) (a:=1228) (b:=1228) (join_sums term (lo:=209604) (a:=614) (b:=614) block209604 block210218) (join_sums term (lo:=210832) (a:=614) (b:=614) block210832 block211446)) (join_sums term (lo:=212060) (a:=1228) (b:=1229) (join_sums term (lo:=212060) (a:=614) (b:=614) block212060 block212674) (join_sums term (lo:=213288) (a:=614) (b:=615) block213288 block213902))))) (join_sums term (lo:=214517) (a:=9825) (b:=9826) (join_sums term (lo:=214517) (a:=4912) (b:=4913) (join_sums term (lo:=214517) (a:=2456) (b:=2456) (join_sums term (lo:=214517) (a:=1228) (b:=1228) (join_sums term (lo:=214517) (a:=614) (b:=614) block214517 block215131) (join_sums term (lo:=215745) (a:=614) (b:=614) block215745 block216359)) (join_sums term (lo:=216973) (a:=1228) (b:=1228) (join_sums term (lo:=216973) (a:=614) (b:=614) block216973 block217587) (join_sums term (lo:=218201) (a:=614) (b:=614) block218201 block218815))) (join_sums term (lo:=219429) (a:=2456) (b:=2457) (join_sums term (lo:=219429) (a:=1228) (b:=1228) (join_sums term (lo:=219429) (a:=614) (b:=614) block219429 block220043) (join_sums term (lo:=220657) (a:=614) (b:=614) block220657 block221271)) (join_sums term (lo:=221885) (a:=1228) (b:=1229) (join_sums term (lo:=221885) (a:=614) (b:=614) block221885 block222499) (join_sums term (lo:=223113) (a:=614) (b:=615) block223113 block223727)))) (join_sums term (lo:=224342) (a:=4913) (b:=4913) (join_sums term (lo:=224342) (a:=2456) (b:=2457) (join_sums term (lo:=224342) (a:=1228) (b:=1228) (join_sums term (lo:=224342) (a:=614) (b:=614) block224342 block224956) (join_sums term (lo:=225570) (a:=614) (b:=614) block225570 block226184)) (join_sums term (lo:=226798) (a:=1228) (b:=1229) (join_sums term (lo:=226798) (a:=614) (b:=614) block226798 block227412) (join_sums term (lo:=228026) (a:=614) (b:=615) block228026 block228640))) (join_sums term (lo:=229255) (a:=2456) (b:=2457) (join_sums term (lo:=229255) (a:=1228) (b:=1228) (join_sums term (lo:=229255) (a:=614) (b:=614) block229255 block229869) (join_sums term (lo:=230483) (a:=614) (b:=614) block230483 block231097)) (join_sums term (lo:=231711) (a:=1228) (b:=1229) (join_sums term (lo:=231711) (a:=614) (b:=614) block231711 block232325) (join_sums term (lo:=232939) (a:=614) (b:=615) block232939 block233553)))))) (join_sums term (lo:=234168) (a:=19651) (b:=19651) (join_sums term (lo:=234168) (a:=9825) (b:=9826) (join_sums term (lo:=234168) (a:=4912) (b:=4913) (join_sums term (lo:=234168) (a:=2456) (b:=2456) (join_sums term (lo:=234168) (a:=1228) (b:=1228) (join_sums term (lo:=234168) (a:=614) (b:=614) block234168 block234782) (join_sums term (lo:=235396) (a:=614) (b:=614) block235396 block236010)) (join_sums term (lo:=236624) (a:=1228) (b:=1228) (join_sums term (lo:=236624) (a:=614) (b:=614) block236624 block237238) (join_sums term (lo:=237852) (a:=614) (b:=614) block237852 block238466))) (join_sums term (lo:=239080) (a:=2456) (b:=2457) (join_sums term (lo:=239080) (a:=1228) (b:=1228) (join_sums term (lo:=239080) (a:=614) (b:=614) block239080 block239694) (join_sums term (lo:=240308) (a:=614) (b:=614) block240308 block240922)) (join_sums term (lo:=241536) (a:=1228) (b:=1229) (join_sums term (lo:=241536) (a:=614) (b:=614) block241536 block242150) (join_sums term (lo:=242764) (a:=614) (b:=615) block242764 block243378)))) (join_sums term (lo:=243993) (a:=4913) (b:=4913) (join_sums term (lo:=243993) (a:=2456) (b:=2457) (join_sums term (lo:=243993) (a:=1228) (b:=1228) (join_sums term (lo:=243993) (a:=614) (b:=614) block243993 block244607) (join_sums term (lo:=245221) (a:=614) (b:=614) block245221 block245835)) (join_sums term (lo:=246449) (a:=1228) (b:=1229) (join_sums term (lo:=246449) (a:=614) (b:=614) block246449 block247063) (join_sums term (lo:=247677) (a:=614) (b:=615) block247677 block248291))) (join_sums term (lo:=248906) (a:=2456) (b:=2457) (join_sums term (lo:=248906) (a:=1228) (b:=1228) (join_sums term (lo:=248906) (a:=614) (b:=614) block248906 block249520) (join_sums term (lo:=250134) (a:=614) (b:=614) block250134 block250748)) (join_sums term (lo:=251362) (a:=1228) (b:=1229) (join_sums term (lo:=251362) (a:=614) (b:=614) block251362 block251976) (join_sums term (lo:=252590) (a:=614) (b:=615) block252590 block253204))))) (join_sums term (lo:=253819) (a:=9825) (b:=9826) (join_sums term (lo:=253819) (a:=4912) (b:=4913) (join_sums term (lo:=253819) (a:=2456) (b:=2456) (join_sums term (lo:=253819) (a:=1228) (b:=1228) (join_sums term (lo:=253819) (a:=614) (b:=614) block253819 block254433) (join_sums term (lo:=255047) (a:=614) (b:=614) block255047 block255661)) (join_sums term (lo:=256275) (a:=1228) (b:=1228) (join_sums term (lo:=256275) (a:=614) (b:=614) block256275 block256889) (join_sums term (lo:=257503) (a:=614) (b:=614) block257503 block258117))) (join_sums term (lo:=258731) (a:=2456) (b:=2457) (join_sums term (lo:=258731) (a:=1228) (b:=1228) (join_sums term (lo:=258731) (a:=614) (b:=614) block258731 block259345) (join_sums term (lo:=259959) (a:=614) (b:=614) block259959 block260573)) (join_sums term (lo:=261187) (a:=1228) (b:=1229) (join_sums term (lo:=261187) (a:=614) (b:=614) block261187 block261801) (join_sums term (lo:=262415) (a:=614) (b:=615) block262415 block263029)))) (join_sums term (lo:=263644) (a:=4913) (b:=4913) (join_sums term (lo:=263644) (a:=2456) (b:=2457) (join_sums term (lo:=263644) (a:=1228) (b:=1228) (join_sums term (lo:=263644) (a:=614) (b:=614) block263644 block264258) (join_sums term (lo:=264872) (a:=614) (b:=614) block264872 block265486)) (join_sums term (lo:=266100) (a:=1228) (b:=1229) (join_sums term (lo:=266100) (a:=614) (b:=614) block266100 block266714) (join_sums term (lo:=267328) (a:=614) (b:=615) block267328 block267942))) (join_sums term (lo:=268557) (a:=2456) (b:=2457) (join_sums term (lo:=268557) (a:=1228) (b:=1228) (join_sums term (lo:=268557) (a:=614) (b:=614) block268557 block269171) (join_sums term (lo:=269785) (a:=614) (b:=614) block269785 block270399)) (join_sums term (lo:=271013) (a:=1228) (b:=1229) (join_sums term (lo:=271013) (a:=614) (b:=614) block271013 block271627) (join_sums term (lo:=272241) (a:=614) (b:=615) block272241 block272855)))))))) (join_sums term (lo:=273470) (a:=78603) (b:=78604) (join_sums term (lo:=273470) (a:=39301) (b:=39302) (join_sums term (lo:=273470) (a:=19650) (b:=19651) (join_sums term (lo:=273470) (a:=9825) (b:=9825) (join_sums term (lo:=273470) (a:=4912) (b:=4913) (join_sums term (lo:=273470) (a:=2456) (b:=2456) (join_sums term (lo:=273470) (a:=1228) (b:=1228) (join_sums term (lo:=273470) (a:=614) (b:=614) block273470 block274084) (join_sums term (lo:=274698) (a:=614) (b:=614) block274698 block275312)) (join_sums term (lo:=275926) (a:=1228) (b:=1228) (join_sums term (lo:=275926) (a:=614) (b:=614) block275926 block276540) (join_sums term (lo:=277154) (a:=614) (b:=614) block277154 block277768))) (join_sums term (lo:=278382) (a:=2456) (b:=2457) (join_sums term (lo:=278382) (a:=1228) (b:=1228) (join_sums term (lo:=278382) (a:=614) (b:=614) block278382 block278996) (join_sums term (lo:=279610) (a:=614) (b:=614) block279610 block280224)) (join_sums term (lo:=280838) (a:=1228) (b:=1229) (join_sums term (lo:=280838) (a:=614) (b:=614) block280838 block281452) (join_sums term (lo:=282066) (a:=614) (b:=615) block282066 block282680)))) (join_sums term (lo:=283295) (a:=4912) (b:=4913) (join_sums term (lo:=283295) (a:=2456) (b:=2456) (join_sums term (lo:=283295) (a:=1228) (b:=1228) (join_sums term (lo:=283295) (a:=614) (b:=614) block283295 block283909) (join_sums term (lo:=284523) (a:=614) (b:=614) block284523 block285137)) (join_sums term (lo:=285751) (a:=1228) (b:=1228) (join_sums term (lo:=285751) (a:=614) (b:=614) block285751 block286365) (join_sums term (lo:=286979) (a:=614) (b:=614) block286979 block287593))) (join_sums term (lo:=288207) (a:=2456) (b:=2457) (join_sums term (lo:=288207) (a:=1228) (b:=1228) (join_sums term (lo:=288207) (a:=614) (b:=614) block288207 block288821) (join_sums term (lo:=289435) (a:=614) (b:=614) block289435 block290049)) (join_sums term (lo:=290663) (a:=1228) (b:=1229) (join_sums term (lo:=290663) (a:=614) (b:=614) block290663 block291277) (join_sums term (lo:=291891) (a:=614) (b:=615) block291891 block292505))))) (join_sums term (lo:=293120) (a:=9825) (b:=9826) (join_sums term (lo:=293120) (a:=4912) (b:=4913) (join_sums term (lo:=293120) (a:=2456) (b:=2456) (join_sums term (lo:=293120) (a:=1228) (b:=1228) (join_sums term (lo:=293120) (a:=614) (b:=614) block293120 block293734) (join_sums term (lo:=294348) (a:=614) (b:=614) block294348 block294962)) (join_sums term (lo:=295576) (a:=1228) (b:=1228) (join_sums term (lo:=295576) (a:=614) (b:=614) block295576 block296190) (join_sums term (lo:=296804) (a:=614) (b:=614) block296804 block297418))) (join_sums term (lo:=298032) (a:=2456) (b:=2457) (join_sums term (lo:=298032) (a:=1228) (b:=1228) (join_sums term (lo:=298032) (a:=614) (b:=614) block298032 block298646) (join_sums term (lo:=299260) (a:=614) (b:=614) block299260 block299874)) (join_sums term (lo:=300488) (a:=1228) (b:=1229) (join_sums term (lo:=300488) (a:=614) (b:=614) block300488 block301102) (join_sums term (lo:=301716) (a:=614) (b:=615) block301716 block302330)))) (join_sums term (lo:=302945) (a:=4913) (b:=4913) (join_sums term (lo:=302945) (a:=2456) (b:=2457) (join_sums term (lo:=302945) (a:=1228) (b:=1228) (join_sums term (lo:=302945) (a:=614) (b:=614) block302945 block303559) (join_sums term (lo:=304173) (a:=614) (b:=614) block304173 block304787)) (join_sums term (lo:=305401) (a:=1228) (b:=1229) (join_sums term (lo:=305401) (a:=614) (b:=614) block305401 block306015) (join_sums term (lo:=306629) (a:=614) (b:=615) block306629 block307243))) (join_sums term (lo:=307858) (a:=2456) (b:=2457) (join_sums term (lo:=307858) (a:=1228) (b:=1228) (join_sums term (lo:=307858) (a:=614) (b:=614) block307858 block308472) (join_sums term (lo:=309086) (a:=614) (b:=614) block309086 block309700)) (join_sums term (lo:=310314) (a:=1228) (b:=1229) (join_sums term (lo:=310314) (a:=614) (b:=614) block310314 block310928) (join_sums term (lo:=311542) (a:=614) (b:=615) block311542 block312156)))))) (join_sums term (lo:=312771) (a:=19651) (b:=19651) (join_sums term (lo:=312771) (a:=9825) (b:=9826) (join_sums term (lo:=312771) (a:=4912) (b:=4913) (join_sums term (lo:=312771) (a:=2456) (b:=2456) (join_sums term (lo:=312771) (a:=1228) (b:=1228) (join_sums term (lo:=312771) (a:=614) (b:=614) block312771 block313385) (join_sums term (lo:=313999) (a:=614) (b:=614) block313999 block314613)) (join_sums term (lo:=315227) (a:=1228) (b:=1228) (join_sums term (lo:=315227) (a:=614) (b:=614) block315227 block315841) (join_sums term (lo:=316455) (a:=614) (b:=614) block316455 block317069))) (join_sums term (lo:=317683) (a:=2456) (b:=2457) (join_sums term (lo:=317683) (a:=1228) (b:=1228) (join_sums term (lo:=317683) (a:=614) (b:=614) block317683 block318297) (join_sums term (lo:=318911) (a:=614) (b:=614) block318911 block319525)) (join_sums term (lo:=320139) (a:=1228) (b:=1229) (join_sums term (lo:=320139) (a:=614) (b:=614) block320139 block320753) (join_sums term (lo:=321367) (a:=614) (b:=615) block321367 block321981)))) (join_sums term (lo:=322596) (a:=4913) (b:=4913) (join_sums term (lo:=322596) (a:=2456) (b:=2457) (join_sums term (lo:=322596) (a:=1228) (b:=1228) (join_sums term (lo:=322596) (a:=614) (b:=614) block322596 block323210) (join_sums term (lo:=323824) (a:=614) (b:=614) block323824 block324438)) (join_sums term (lo:=325052) (a:=1228) (b:=1229) (join_sums term (lo:=325052) (a:=614) (b:=614) block325052 block325666) (join_sums term (lo:=326280) (a:=614) (b:=615) block326280 block326894))) (join_sums term (lo:=327509) (a:=2456) (b:=2457) (join_sums term (lo:=327509) (a:=1228) (b:=1228) (join_sums term (lo:=327509) (a:=614) (b:=614) block327509 block328123) (join_sums term (lo:=328737) (a:=614) (b:=614) block328737 block329351)) (join_sums term (lo:=329965) (a:=1228) (b:=1229) (join_sums term (lo:=329965) (a:=614) (b:=614) block329965 block330579) (join_sums term (lo:=331193) (a:=614) (b:=615) block331193 block331807))))) (join_sums term (lo:=332422) (a:=9825) (b:=9826) (join_sums term (lo:=332422) (a:=4912) (b:=4913) (join_sums term (lo:=332422) (a:=2456) (b:=2456) (join_sums term (lo:=332422) (a:=1228) (b:=1228) (join_sums term (lo:=332422) (a:=614) (b:=614) block332422 block333036) (join_sums term (lo:=333650) (a:=614) (b:=614) block333650 block334264)) (join_sums term (lo:=334878) (a:=1228) (b:=1228) (join_sums term (lo:=334878) (a:=614) (b:=614) block334878 block335492) (join_sums term (lo:=336106) (a:=614) (b:=614) block336106 block336720))) (join_sums term (lo:=337334) (a:=2456) (b:=2457) (join_sums term (lo:=337334) (a:=1228) (b:=1228) (join_sums term (lo:=337334) (a:=614) (b:=614) block337334 block337948) (join_sums term (lo:=338562) (a:=614) (b:=614) block338562 block339176)) (join_sums term (lo:=339790) (a:=1228) (b:=1229) (join_sums term (lo:=339790) (a:=614) (b:=614) block339790 block340404) (join_sums term (lo:=341018) (a:=614) (b:=615) block341018 block341632)))) (join_sums term (lo:=342247) (a:=4913) (b:=4913) (join_sums term (lo:=342247) (a:=2456) (b:=2457) (join_sums term (lo:=342247) (a:=1228) (b:=1228) (join_sums term (lo:=342247) (a:=614) (b:=614) block342247 block342861) (join_sums term (lo:=343475) (a:=614) (b:=614) block343475 block344089)) (join_sums term (lo:=344703) (a:=1228) (b:=1229) (join_sums term (lo:=344703) (a:=614) (b:=614) block344703 block345317) (join_sums term (lo:=345931) (a:=614) (b:=615) block345931 block346545))) (join_sums term (lo:=347160) (a:=2456) (b:=2457) (join_sums term (lo:=347160) (a:=1228) (b:=1228) (join_sums term (lo:=347160) (a:=614) (b:=614) block347160 block347774) (join_sums term (lo:=348388) (a:=614) (b:=614) block348388 block349002)) (join_sums term (lo:=349616) (a:=1228) (b:=1229) (join_sums term (lo:=349616) (a:=614) (b:=614) block349616 block350230) (join_sums term (lo:=350844) (a:=614) (b:=615) block350844 block351458))))))) (join_sums term (lo:=352073) (a:=39302) (b:=39302) (join_sums term (lo:=352073) (a:=19651) (b:=19651) (join_sums term (lo:=352073) (a:=9825) (b:=9826) (join_sums term (lo:=352073) (a:=4912) (b:=4913) (join_sums term (lo:=352073) (a:=2456) (b:=2456) (join_sums term (lo:=352073) (a:=1228) (b:=1228) (join_sums term (lo:=352073) (a:=614) (b:=614) block352073 block352687) (join_sums term (lo:=353301) (a:=614) (b:=614) block353301 block353915)) (join_sums term (lo:=354529) (a:=1228) (b:=1228) (join_sums term (lo:=354529) (a:=614) (b:=614) block354529 block355143) (join_sums term (lo:=355757) (a:=614) (b:=614) block355757 block356371))) (join_sums term (lo:=356985) (a:=2456) (b:=2457) (join_sums term (lo:=356985) (a:=1228) (b:=1228) (join_sums term (lo:=356985) (a:=614) (b:=614) block356985 block357599) (join_sums term (lo:=358213) (a:=614) (b:=614) block358213 block358827)) (join_sums term (lo:=359441) (a:=1228) (b:=1229) (join_sums term (lo:=359441) (a:=614) (b:=614) block359441 block360055) (join_sums term (lo:=360669) (a:=614) (b:=615) block360669 block361283)))) (join_sums term (lo:=361898) (a:=4913) (b:=4913) (join_sums term (lo:=361898) (a:=2456) (b:=2457) (join_sums term (lo:=361898) (a:=1228) (b:=1228) (join_sums term (lo:=361898) (a:=614) (b:=614) block361898 block362512) (join_sums term (lo:=363126) (a:=614) (b:=614) block363126 block363740)) (join_sums term (lo:=364354) (a:=1228) (b:=1229) (join_sums term (lo:=364354) (a:=614) (b:=614) block364354 block364968) (join_sums term (lo:=365582) (a:=614) (b:=615) block365582 block366196))) (join_sums term (lo:=366811) (a:=2456) (b:=2457) (join_sums term (lo:=366811) (a:=1228) (b:=1228) (join_sums term (lo:=366811) (a:=614) (b:=614) block366811 block367425) (join_sums term (lo:=368039) (a:=614) (b:=614) block368039 block368653)) (join_sums term (lo:=369267) (a:=1228) (b:=1229) (join_sums term (lo:=369267) (a:=614) (b:=614) block369267 block369881) (join_sums term (lo:=370495) (a:=614) (b:=615) block370495 block371109))))) (join_sums term (lo:=371724) (a:=9825) (b:=9826) (join_sums term (lo:=371724) (a:=4912) (b:=4913) (join_sums term (lo:=371724) (a:=2456) (b:=2456) (join_sums term (lo:=371724) (a:=1228) (b:=1228) (join_sums term (lo:=371724) (a:=614) (b:=614) block371724 block372338) (join_sums term (lo:=372952) (a:=614) (b:=614) block372952 block373566)) (join_sums term (lo:=374180) (a:=1228) (b:=1228) (join_sums term (lo:=374180) (a:=614) (b:=614) block374180 block374794) (join_sums term (lo:=375408) (a:=614) (b:=614) block375408 block376022))) (join_sums term (lo:=376636) (a:=2456) (b:=2457) (join_sums term (lo:=376636) (a:=1228) (b:=1228) (join_sums term (lo:=376636) (a:=614) (b:=614) block376636 block377250) (join_sums term (lo:=377864) (a:=614) (b:=614) block377864 block378478)) (join_sums term (lo:=379092) (a:=1228) (b:=1229) (join_sums term (lo:=379092) (a:=614) (b:=614) block379092 block379706) (join_sums term (lo:=380320) (a:=614) (b:=615) block380320 block380934)))) (join_sums term (lo:=381549) (a:=4913) (b:=4913) (join_sums term (lo:=381549) (a:=2456) (b:=2457) (join_sums term (lo:=381549) (a:=1228) (b:=1228) (join_sums term (lo:=381549) (a:=614) (b:=614) block381549 block382163) (join_sums term (lo:=382777) (a:=614) (b:=614) block382777 block383391)) (join_sums term (lo:=384005) (a:=1228) (b:=1229) (join_sums term (lo:=384005) (a:=614) (b:=614) block384005 block384619) (join_sums term (lo:=385233) (a:=614) (b:=615) block385233 block385847))) (join_sums term (lo:=386462) (a:=2456) (b:=2457) (join_sums term (lo:=386462) (a:=1228) (b:=1228) (join_sums term (lo:=386462) (a:=614) (b:=614) block386462 block387076) (join_sums term (lo:=387690) (a:=614) (b:=614) block387690 block388304)) (join_sums term (lo:=388918) (a:=1228) (b:=1229) (join_sums term (lo:=388918) (a:=614) (b:=614) block388918 block389532) (join_sums term (lo:=390146) (a:=614) (b:=615) block390146 block390760)))))) (join_sums term (lo:=391375) (a:=19651) (b:=19651) (join_sums term (lo:=391375) (a:=9825) (b:=9826) (join_sums term (lo:=391375) (a:=4912) (b:=4913) (join_sums term (lo:=391375) (a:=2456) (b:=2456) (join_sums term (lo:=391375) (a:=1228) (b:=1228) (join_sums term (lo:=391375) (a:=614) (b:=614) block391375 block391989) (join_sums term (lo:=392603) (a:=614) (b:=614) block392603 block393217)) (join_sums term (lo:=393831) (a:=1228) (b:=1228) (join_sums term (lo:=393831) (a:=614) (b:=614) block393831 block394445) (join_sums term (lo:=395059) (a:=614) (b:=614) block395059 block395673))) (join_sums term (lo:=396287) (a:=2456) (b:=2457) (join_sums term (lo:=396287) (a:=1228) (b:=1228) (join_sums term (lo:=396287) (a:=614) (b:=614) block396287 block396901) (join_sums term (lo:=397515) (a:=614) (b:=614) block397515 block398129)) (join_sums term (lo:=398743) (a:=1228) (b:=1229) (join_sums term (lo:=398743) (a:=614) (b:=614) block398743 block399357) (join_sums term (lo:=399971) (a:=614) (b:=615) block399971 block400585)))) (join_sums term (lo:=401200) (a:=4913) (b:=4913) (join_sums term (lo:=401200) (a:=2456) (b:=2457) (join_sums term (lo:=401200) (a:=1228) (b:=1228) (join_sums term (lo:=401200) (a:=614) (b:=614) block401200 block401814) (join_sums term (lo:=402428) (a:=614) (b:=614) block402428 block403042)) (join_sums term (lo:=403656) (a:=1228) (b:=1229) (join_sums term (lo:=403656) (a:=614) (b:=614) block403656 block404270) (join_sums term (lo:=404884) (a:=614) (b:=615) block404884 block405498))) (join_sums term (lo:=406113) (a:=2456) (b:=2457) (join_sums term (lo:=406113) (a:=1228) (b:=1228) (join_sums term (lo:=406113) (a:=614) (b:=614) block406113 block406727) (join_sums term (lo:=407341) (a:=614) (b:=614) block407341 block407955)) (join_sums term (lo:=408569) (a:=1228) (b:=1229) (join_sums term (lo:=408569) (a:=614) (b:=614) block408569 block409183) (join_sums term (lo:=409797) (a:=614) (b:=615) block409797 block410411))))) (join_sums term (lo:=411026) (a:=9825) (b:=9826) (join_sums term (lo:=411026) (a:=4912) (b:=4913) (join_sums term (lo:=411026) (a:=2456) (b:=2456) (join_sums term (lo:=411026) (a:=1228) (b:=1228) (join_sums term (lo:=411026) (a:=614) (b:=614) block411026 block411640) (join_sums term (lo:=412254) (a:=614) (b:=614) block412254 block412868)) (join_sums term (lo:=413482) (a:=1228) (b:=1228) (join_sums term (lo:=413482) (a:=614) (b:=614) block413482 block414096) (join_sums term (lo:=414710) (a:=614) (b:=614) block414710 block415324))) (join_sums term (lo:=415938) (a:=2456) (b:=2457) (join_sums term (lo:=415938) (a:=1228) (b:=1228) (join_sums term (lo:=415938) (a:=614) (b:=614) block415938 block416552) (join_sums term (lo:=417166) (a:=614) (b:=614) block417166 block417780)) (join_sums term (lo:=418394) (a:=1228) (b:=1229) (join_sums term (lo:=418394) (a:=614) (b:=614) block418394 block419008) (join_sums term (lo:=419622) (a:=614) (b:=615) block419622 block420236)))) (join_sums term (lo:=420851) (a:=4913) (b:=4913) (join_sums term (lo:=420851) (a:=2456) (b:=2457) (join_sums term (lo:=420851) (a:=1228) (b:=1228) (join_sums term (lo:=420851) (a:=614) (b:=614) block420851 block421465) (join_sums term (lo:=422079) (a:=614) (b:=614) block422079 block422693)) (join_sums term (lo:=423307) (a:=1228) (b:=1229) (join_sums term (lo:=423307) (a:=614) (b:=614) block423307 block423921) (join_sums term (lo:=424535) (a:=614) (b:=615) block424535 block425149))) (join_sums term (lo:=425764) (a:=2456) (b:=2457) (join_sums term (lo:=425764) (a:=1228) (b:=1228) (join_sums term (lo:=425764) (a:=614) (b:=614) block425764 block426378) (join_sums term (lo:=426992) (a:=614) (b:=614) block426992 block427606)) (join_sums term (lo:=428220) (a:=1228) (b:=1229) (join_sums term (lo:=428220) (a:=614) (b:=614) block428220 block428834) (join_sums term (lo:=429448) (a:=614) (b:=615) block429448 block430062))))))))) (join_sums term (lo:=430677) (a:=157206) (b:=157207) (join_sums term (lo:=430677) (a:=78603) (b:=78603) (join_sums term (lo:=430677) (a:=39301) (b:=39302) (join_sums term (lo:=430677) (a:=19650) (b:=19651) (join_sums term (lo:=430677) (a:=9825) (b:=9825) (join_sums term (lo:=430677) (a:=4912) (b:=4913) (join_sums term (lo:=430677) (a:=2456) (b:=2456) (join_sums term (lo:=430677) (a:=1228) (b:=1228) (join_sums term (lo:=430677) (a:=614) (b:=614) block430677 block431291) (join_sums term (lo:=431905) (a:=614) (b:=614) block431905 block432519)) (join_sums term (lo:=433133) (a:=1228) (b:=1228) (join_sums term (lo:=433133) (a:=614) (b:=614) block433133 block433747) (join_sums term (lo:=434361) (a:=614) (b:=614) block434361 block434975))) (join_sums term (lo:=435589) (a:=2456) (b:=2457) (join_sums term (lo:=435589) (a:=1228) (b:=1228) (join_sums term (lo:=435589) (a:=614) (b:=614) block435589 block436203) (join_sums term (lo:=436817) (a:=614) (b:=614) block436817 block437431)) (join_sums term (lo:=438045) (a:=1228) (b:=1229) (join_sums term (lo:=438045) (a:=614) (b:=614) block438045 block438659) (join_sums term (lo:=439273) (a:=614) (b:=615) block439273 block439887)))) (join_sums term (lo:=440502) (a:=4912) (b:=4913) (join_sums term (lo:=440502) (a:=2456) (b:=2456) (join_sums term (lo:=440502) (a:=1228) (b:=1228) (join_sums term (lo:=440502) (a:=614) (b:=614) block440502 block441116) (join_sums term (lo:=441730) (a:=614) (b:=614) block441730 block442344)) (join_sums term (lo:=442958) (a:=1228) (b:=1228) (join_sums term (lo:=442958) (a:=614) (b:=614) block442958 block443572) (join_sums term (lo:=444186) (a:=614) (b:=614) block444186 block444800))) (join_sums term (lo:=445414) (a:=2456) (b:=2457) (join_sums term (lo:=445414) (a:=1228) (b:=1228) (join_sums term (lo:=445414) (a:=614) (b:=614) block445414 block446028) (join_sums term (lo:=446642) (a:=614) (b:=614) block446642 block447256)) (join_sums term (lo:=447870) (a:=1228) (b:=1229) (join_sums term (lo:=447870) (a:=614) (b:=614) block447870 block448484) (join_sums term (lo:=449098) (a:=614) (b:=615) block449098 block449712))))) (join_sums term (lo:=450327) (a:=9825) (b:=9826) (join_sums term (lo:=450327) (a:=4912) (b:=4913) (join_sums term (lo:=450327) (a:=2456) (b:=2456) (join_sums term (lo:=450327) (a:=1228) (b:=1228) (join_sums term (lo:=450327) (a:=614) (b:=614) block450327 block450941) (join_sums term (lo:=451555) (a:=614) (b:=614) block451555 block452169)) (join_sums term (lo:=452783) (a:=1228) (b:=1228) (join_sums term (lo:=452783) (a:=614) (b:=614) block452783 block453397) (join_sums term (lo:=454011) (a:=614) (b:=614) block454011 block454625))) (join_sums term (lo:=455239) (a:=2456) (b:=2457) (join_sums term (lo:=455239) (a:=1228) (b:=1228) (join_sums term (lo:=455239) (a:=614) (b:=614) block455239 block455853) (join_sums term (lo:=456467) (a:=614) (b:=614) block456467 block457081)) (join_sums term (lo:=457695) (a:=1228) (b:=1229) (join_sums term (lo:=457695) (a:=614) (b:=614) block457695 block458309) (join_sums term (lo:=458923) (a:=614) (b:=615) block458923 block459537)))) (join_sums term (lo:=460152) (a:=4913) (b:=4913) (join_sums term (lo:=460152) (a:=2456) (b:=2457) (join_sums term (lo:=460152) (a:=1228) (b:=1228) (join_sums term (lo:=460152) (a:=614) (b:=614) block460152 block460766) (join_sums term (lo:=461380) (a:=614) (b:=614) block461380 block461994)) (join_sums term (lo:=462608) (a:=1228) (b:=1229) (join_sums term (lo:=462608) (a:=614) (b:=614) block462608 block463222) (join_sums term (lo:=463836) (a:=614) (b:=615) block463836 block464450))) (join_sums term (lo:=465065) (a:=2456) (b:=2457) (join_sums term (lo:=465065) (a:=1228) (b:=1228) (join_sums term (lo:=465065) (a:=614) (b:=614) block465065 block465679) (join_sums term (lo:=466293) (a:=614) (b:=614) block466293 block466907)) (join_sums term (lo:=467521) (a:=1228) (b:=1229) (join_sums term (lo:=467521) (a:=614) (b:=614) block467521 block468135) (join_sums term (lo:=468749) (a:=614) (b:=615) block468749 block469363)))))) (join_sums term (lo:=469978) (a:=19651) (b:=19651) (join_sums term (lo:=469978) (a:=9825) (b:=9826) (join_sums term (lo:=469978) (a:=4912) (b:=4913) (join_sums term (lo:=469978) (a:=2456) (b:=2456) (join_sums term (lo:=469978) (a:=1228) (b:=1228) (join_sums term (lo:=469978) (a:=614) (b:=614) block469978 block470592) (join_sums term (lo:=471206) (a:=614) (b:=614) block471206 block471820)) (join_sums term (lo:=472434) (a:=1228) (b:=1228) (join_sums term (lo:=472434) (a:=614) (b:=614) block472434 block473048) (join_sums term (lo:=473662) (a:=614) (b:=614) block473662 block474276))) (join_sums term (lo:=474890) (a:=2456) (b:=2457) (join_sums term (lo:=474890) (a:=1228) (b:=1228) (join_sums term (lo:=474890) (a:=614) (b:=614) block474890 block475504) (join_sums term (lo:=476118) (a:=614) (b:=614) block476118 block476732)) (join_sums term (lo:=477346) (a:=1228) (b:=1229) (join_sums term (lo:=477346) (a:=614) (b:=614) block477346 block477960) (join_sums term (lo:=478574) (a:=614) (b:=615) block478574 block479188)))) (join_sums term (lo:=479803) (a:=4913) (b:=4913) (join_sums term (lo:=479803) (a:=2456) (b:=2457) (join_sums term (lo:=479803) (a:=1228) (b:=1228) (join_sums term (lo:=479803) (a:=614) (b:=614) block479803 block480417) (join_sums term (lo:=481031) (a:=614) (b:=614) block481031 block481645)) (join_sums term (lo:=482259) (a:=1228) (b:=1229) (join_sums term (lo:=482259) (a:=614) (b:=614) block482259 block482873) (join_sums term (lo:=483487) (a:=614) (b:=615) block483487 block484101))) (join_sums term (lo:=484716) (a:=2456) (b:=2457) (join_sums term (lo:=484716) (a:=1228) (b:=1228) (join_sums term (lo:=484716) (a:=614) (b:=614) block484716 block485330) (join_sums term (lo:=485944) (a:=614) (b:=614) block485944 block486558)) (join_sums term (lo:=487172) (a:=1228) (b:=1229) (join_sums term (lo:=487172) (a:=614) (b:=614) block487172 block487786) (join_sums term (lo:=488400) (a:=614) (b:=615) block488400 block489014))))) (join_sums term (lo:=489629) (a:=9825) (b:=9826) (join_sums term (lo:=489629) (a:=4912) (b:=4913) (join_sums term (lo:=489629) (a:=2456) (b:=2456) (join_sums term (lo:=489629) (a:=1228) (b:=1228) (join_sums term (lo:=489629) (a:=614) (b:=614) block489629 block490243) (join_sums term (lo:=490857) (a:=614) (b:=614) block490857 block491471)) (join_sums term (lo:=492085) (a:=1228) (b:=1228) (join_sums term (lo:=492085) (a:=614) (b:=614) block492085 block492699) (join_sums term (lo:=493313) (a:=614) (b:=614) block493313 block493927))) (join_sums term (lo:=494541) (a:=2456) (b:=2457) (join_sums term (lo:=494541) (a:=1228) (b:=1228) (join_sums term (lo:=494541) (a:=614) (b:=614) block494541 block495155) (join_sums term (lo:=495769) (a:=614) (b:=614) block495769 block496383)) (join_sums term (lo:=496997) (a:=1228) (b:=1229) (join_sums term (lo:=496997) (a:=614) (b:=614) block496997 block497611) (join_sums term (lo:=498225) (a:=614) (b:=615) block498225 block498839)))) (join_sums term (lo:=499454) (a:=4913) (b:=4913) (join_sums term (lo:=499454) (a:=2456) (b:=2457) (join_sums term (lo:=499454) (a:=1228) (b:=1228) (join_sums term (lo:=499454) (a:=614) (b:=614) block499454 block500068) (join_sums term (lo:=500682) (a:=614) (b:=614) block500682 block501296)) (join_sums term (lo:=501910) (a:=1228) (b:=1229) (join_sums term (lo:=501910) (a:=614) (b:=614) block501910 block502524) (join_sums term (lo:=503138) (a:=614) (b:=615) block503138 block503752))) (join_sums term (lo:=504367) (a:=2456) (b:=2457) (join_sums term (lo:=504367) (a:=1228) (b:=1228) (join_sums term (lo:=504367) (a:=614) (b:=614) block504367 block504981) (join_sums term (lo:=505595) (a:=614) (b:=614) block505595 block506209)) (join_sums term (lo:=506823) (a:=1228) (b:=1229) (join_sums term (lo:=506823) (a:=614) (b:=614) block506823 block507437) (join_sums term (lo:=508051) (a:=614) (b:=615) block508051 block508665))))))) (join_sums term (lo:=509280) (a:=39301) (b:=39302) (join_sums term (lo:=509280) (a:=19650) (b:=19651) (join_sums term (lo:=509280) (a:=9825) (b:=9825) (join_sums term (lo:=509280) (a:=4912) (b:=4913) (join_sums term (lo:=509280) (a:=2456) (b:=2456) (join_sums term (lo:=509280) (a:=1228) (b:=1228) (join_sums term (lo:=509280) (a:=614) (b:=614) block509280 block509894) (join_sums term (lo:=510508) (a:=614) (b:=614) block510508 block511122)) (join_sums term (lo:=511736) (a:=1228) (b:=1228) (join_sums term (lo:=511736) (a:=614) (b:=614) block511736 block512350) (join_sums term (lo:=512964) (a:=614) (b:=614) block512964 block513578))) (join_sums term (lo:=514192) (a:=2456) (b:=2457) (join_sums term (lo:=514192) (a:=1228) (b:=1228) (join_sums term (lo:=514192) (a:=614) (b:=614) block514192 block514806) (join_sums term (lo:=515420) (a:=614) (b:=614) block515420 block516034)) (join_sums term (lo:=516648) (a:=1228) (b:=1229) (join_sums term (lo:=516648) (a:=614) (b:=614) block516648 block517262) (join_sums term (lo:=517876) (a:=614) (b:=615) block517876 block518490)))) (join_sums term (lo:=519105) (a:=4912) (b:=4913) (join_sums term (lo:=519105) (a:=2456) (b:=2456) (join_sums term (lo:=519105) (a:=1228) (b:=1228) (join_sums term (lo:=519105) (a:=614) (b:=614) block519105 block519719) (join_sums term (lo:=520333) (a:=614) (b:=614) block520333 block520947)) (join_sums term (lo:=521561) (a:=1228) (b:=1228) (join_sums term (lo:=521561) (a:=614) (b:=614) block521561 block522175) (join_sums term (lo:=522789) (a:=614) (b:=614) block522789 block523403))) (join_sums term (lo:=524017) (a:=2456) (b:=2457) (join_sums term (lo:=524017) (a:=1228) (b:=1228) (join_sums term (lo:=524017) (a:=614) (b:=614) block524017 block524631) (join_sums term (lo:=525245) (a:=614) (b:=614) block525245 block525859)) (join_sums term (lo:=526473) (a:=1228) (b:=1229) (join_sums term (lo:=526473) (a:=614) (b:=614) block526473 block527087) (join_sums term (lo:=527701) (a:=614) (b:=615) block527701 block528315))))) (join_sums term (lo:=528930) (a:=9825) (b:=9826) (join_sums term (lo:=528930) (a:=4912) (b:=4913) (join_sums term (lo:=528930) (a:=2456) (b:=2456) (join_sums term (lo:=528930) (a:=1228) (b:=1228) (join_sums term (lo:=528930) (a:=614) (b:=614) block528930 block529544) (join_sums term (lo:=530158) (a:=614) (b:=614) block530158 block530772)) (join_sums term (lo:=531386) (a:=1228) (b:=1228) (join_sums term (lo:=531386) (a:=614) (b:=614) block531386 block532000) (join_sums term (lo:=532614) (a:=614) (b:=614) block532614 block533228))) (join_sums term (lo:=533842) (a:=2456) (b:=2457) (join_sums term (lo:=533842) (a:=1228) (b:=1228) (join_sums term (lo:=533842) (a:=614) (b:=614) block533842 block534456) (join_sums term (lo:=535070) (a:=614) (b:=614) block535070 block535684)) (join_sums term (lo:=536298) (a:=1228) (b:=1229) (join_sums term (lo:=536298) (a:=614) (b:=614) block536298 block536912) (join_sums term (lo:=537526) (a:=614) (b:=615) block537526 block538140)))) (join_sums term (lo:=538755) (a:=4913) (b:=4913) (join_sums term (lo:=538755) (a:=2456) (b:=2457) (join_sums term (lo:=538755) (a:=1228) (b:=1228) (join_sums term (lo:=538755) (a:=614) (b:=614) block538755 block539369) (join_sums term (lo:=539983) (a:=614) (b:=614) block539983 block540597)) (join_sums term (lo:=541211) (a:=1228) (b:=1229) (join_sums term (lo:=541211) (a:=614) (b:=614) block541211 block541825) (join_sums term (lo:=542439) (a:=614) (b:=615) block542439 block543053))) (join_sums term (lo:=543668) (a:=2456) (b:=2457) (join_sums term (lo:=543668) (a:=1228) (b:=1228) (join_sums term (lo:=543668) (a:=614) (b:=614) block543668 block544282) (join_sums term (lo:=544896) (a:=614) (b:=614) block544896 block545510)) (join_sums term (lo:=546124) (a:=1228) (b:=1229) (join_sums term (lo:=546124) (a:=614) (b:=614) block546124 block546738) (join_sums term (lo:=547352) (a:=614) (b:=615) block547352 block547966)))))) (join_sums term (lo:=548581) (a:=19651) (b:=19651) (join_sums term (lo:=548581) (a:=9825) (b:=9826) (join_sums term (lo:=548581) (a:=4912) (b:=4913) (join_sums term (lo:=548581) (a:=2456) (b:=2456) (join_sums term (lo:=548581) (a:=1228) (b:=1228) (join_sums term (lo:=548581) (a:=614) (b:=614) block548581 block549195) (join_sums term (lo:=549809) (a:=614) (b:=614) block549809 block550423)) (join_sums term (lo:=551037) (a:=1228) (b:=1228) (join_sums term (lo:=551037) (a:=614) (b:=614) block551037 block551651) (join_sums term (lo:=552265) (a:=614) (b:=614) block552265 block552879))) (join_sums term (lo:=553493) (a:=2456) (b:=2457) (join_sums term (lo:=553493) (a:=1228) (b:=1228) (join_sums term (lo:=553493) (a:=614) (b:=614) block553493 block554107) (join_sums term (lo:=554721) (a:=614) (b:=614) block554721 block555335)) (join_sums term (lo:=555949) (a:=1228) (b:=1229) (join_sums term (lo:=555949) (a:=614) (b:=614) block555949 block556563) (join_sums term (lo:=557177) (a:=614) (b:=615) block557177 block557791)))) (join_sums term (lo:=558406) (a:=4913) (b:=4913) (join_sums term (lo:=558406) (a:=2456) (b:=2457) (join_sums term (lo:=558406) (a:=1228) (b:=1228) (join_sums term (lo:=558406) (a:=614) (b:=614) block558406 block559020) (join_sums term (lo:=559634) (a:=614) (b:=614) block559634 block560248)) (join_sums term (lo:=560862) (a:=1228) (b:=1229) (join_sums term (lo:=560862) (a:=614) (b:=614) block560862 block561476) (join_sums term (lo:=562090) (a:=614) (b:=615) block562090 block562704))) (join_sums term (lo:=563319) (a:=2456) (b:=2457) (join_sums term (lo:=563319) (a:=1228) (b:=1228) (join_sums term (lo:=563319) (a:=614) (b:=614) block563319 block563933) (join_sums term (lo:=564547) (a:=614) (b:=614) block564547 block565161)) (join_sums term (lo:=565775) (a:=1228) (b:=1229) (join_sums term (lo:=565775) (a:=614) (b:=614) block565775 block566389) (join_sums term (lo:=567003) (a:=614) (b:=615) block567003 block567617))))) (join_sums term (lo:=568232) (a:=9825) (b:=9826) (join_sums term (lo:=568232) (a:=4912) (b:=4913) (join_sums term (lo:=568232) (a:=2456) (b:=2456) (join_sums term (lo:=568232) (a:=1228) (b:=1228) (join_sums term (lo:=568232) (a:=614) (b:=614) block568232 block568846) (join_sums term (lo:=569460) (a:=614) (b:=614) block569460 block570074)) (join_sums term (lo:=570688) (a:=1228) (b:=1228) (join_sums term (lo:=570688) (a:=614) (b:=614) block570688 block571302) (join_sums term (lo:=571916) (a:=614) (b:=614) block571916 block572530))) (join_sums term (lo:=573144) (a:=2456) (b:=2457) (join_sums term (lo:=573144) (a:=1228) (b:=1228) (join_sums term (lo:=573144) (a:=614) (b:=614) block573144 block573758) (join_sums term (lo:=574372) (a:=614) (b:=614) block574372 block574986)) (join_sums term (lo:=575600) (a:=1228) (b:=1229) (join_sums term (lo:=575600) (a:=614) (b:=614) block575600 block576214) (join_sums term (lo:=576828) (a:=614) (b:=615) block576828 block577442)))) (join_sums term (lo:=578057) (a:=4913) (b:=4913) (join_sums term (lo:=578057) (a:=2456) (b:=2457) (join_sums term (lo:=578057) (a:=1228) (b:=1228) (join_sums term (lo:=578057) (a:=614) (b:=614) block578057 block578671) (join_sums term (lo:=579285) (a:=614) (b:=614) block579285 block579899)) (join_sums term (lo:=580513) (a:=1228) (b:=1229) (join_sums term (lo:=580513) (a:=614) (b:=614) block580513 block581127) (join_sums term (lo:=581741) (a:=614) (b:=615) block581741 block582355))) (join_sums term (lo:=582970) (a:=2456) (b:=2457) (join_sums term (lo:=582970) (a:=1228) (b:=1228) (join_sums term (lo:=582970) (a:=614) (b:=614) block582970 block583584) (join_sums term (lo:=584198) (a:=614) (b:=614) block584198 block584812)) (join_sums term (lo:=585426) (a:=1228) (b:=1229) (join_sums term (lo:=585426) (a:=614) (b:=614) block585426 block586040) (join_sums term (lo:=586654) (a:=614) (b:=615) block586654 block587268)))))))) (join_sums term (lo:=587883) (a:=78603) (b:=78604) (join_sums term (lo:=587883) (a:=39301) (b:=39302) (join_sums term (lo:=587883) (a:=19650) (b:=19651) (join_sums term (lo:=587883) (a:=9825) (b:=9825) (join_sums term (lo:=587883) (a:=4912) (b:=4913) (join_sums term (lo:=587883) (a:=2456) (b:=2456) (join_sums term (lo:=587883) (a:=1228) (b:=1228) (join_sums term (lo:=587883) (a:=614) (b:=614) block587883 block588497) (join_sums term (lo:=589111) (a:=614) (b:=614) block589111 block589725)) (join_sums term (lo:=590339) (a:=1228) (b:=1228) (join_sums term (lo:=590339) (a:=614) (b:=614) block590339 block590953) (join_sums term (lo:=591567) (a:=614) (b:=614) block591567 block592181))) (join_sums term (lo:=592795) (a:=2456) (b:=2457) (join_sums term (lo:=592795) (a:=1228) (b:=1228) (join_sums term (lo:=592795) (a:=614) (b:=614) block592795 block593409) (join_sums term (lo:=594023) (a:=614) (b:=614) block594023 block594637)) (join_sums term (lo:=595251) (a:=1228) (b:=1229) (join_sums term (lo:=595251) (a:=614) (b:=614) block595251 block595865) (join_sums term (lo:=596479) (a:=614) (b:=615) block596479 block597093)))) (join_sums term (lo:=597708) (a:=4912) (b:=4913) (join_sums term (lo:=597708) (a:=2456) (b:=2456) (join_sums term (lo:=597708) (a:=1228) (b:=1228) (join_sums term (lo:=597708) (a:=614) (b:=614) block597708 block598322) (join_sums term (lo:=598936) (a:=614) (b:=614) block598936 block599550)) (join_sums term (lo:=600164) (a:=1228) (b:=1228) (join_sums term (lo:=600164) (a:=614) (b:=614) block600164 block600778) (join_sums term (lo:=601392) (a:=614) (b:=614) block601392 block602006))) (join_sums term (lo:=602620) (a:=2456) (b:=2457) (join_sums term (lo:=602620) (a:=1228) (b:=1228) (join_sums term (lo:=602620) (a:=614) (b:=614) block602620 block603234) (join_sums term (lo:=603848) (a:=614) (b:=614) block603848 block604462)) (join_sums term (lo:=605076) (a:=1228) (b:=1229) (join_sums term (lo:=605076) (a:=614) (b:=614) block605076 block605690) (join_sums term (lo:=606304) (a:=614) (b:=615) block606304 block606918))))) (join_sums term (lo:=607533) (a:=9825) (b:=9826) (join_sums term (lo:=607533) (a:=4912) (b:=4913) (join_sums term (lo:=607533) (a:=2456) (b:=2456) (join_sums term (lo:=607533) (a:=1228) (b:=1228) (join_sums term (lo:=607533) (a:=614) (b:=614) block607533 block608147) (join_sums term (lo:=608761) (a:=614) (b:=614) block608761 block609375)) (join_sums term (lo:=609989) (a:=1228) (b:=1228) (join_sums term (lo:=609989) (a:=614) (b:=614) block609989 block610603) (join_sums term (lo:=611217) (a:=614) (b:=614) block611217 block611831))) (join_sums term (lo:=612445) (a:=2456) (b:=2457) (join_sums term (lo:=612445) (a:=1228) (b:=1228) (join_sums term (lo:=612445) (a:=614) (b:=614) block612445 block613059) (join_sums term (lo:=613673) (a:=614) (b:=614) block613673 block614287)) (join_sums term (lo:=614901) (a:=1228) (b:=1229) (join_sums term (lo:=614901) (a:=614) (b:=614) block614901 block615515) (join_sums term (lo:=616129) (a:=614) (b:=615) block616129 block616743)))) (join_sums term (lo:=617358) (a:=4913) (b:=4913) (join_sums term (lo:=617358) (a:=2456) (b:=2457) (join_sums term (lo:=617358) (a:=1228) (b:=1228) (join_sums term (lo:=617358) (a:=614) (b:=614) block617358 block617972) (join_sums term (lo:=618586) (a:=614) (b:=614) block618586 block619200)) (join_sums term (lo:=619814) (a:=1228) (b:=1229) (join_sums term (lo:=619814) (a:=614) (b:=614) block619814 block620428) (join_sums term (lo:=621042) (a:=614) (b:=615) block621042 block621656))) (join_sums term (lo:=622271) (a:=2456) (b:=2457) (join_sums term (lo:=622271) (a:=1228) (b:=1228) (join_sums term (lo:=622271) (a:=614) (b:=614) block622271 block622885) (join_sums term (lo:=623499) (a:=614) (b:=614) block623499 block624113)) (join_sums term (lo:=624727) (a:=1228) (b:=1229) (join_sums term (lo:=624727) (a:=614) (b:=614) block624727 block625341) (join_sums term (lo:=625955) (a:=614) (b:=615) block625955 block626569)))))) (join_sums term (lo:=627184) (a:=19651) (b:=19651) (join_sums term (lo:=627184) (a:=9825) (b:=9826) (join_sums term (lo:=627184) (a:=4912) (b:=4913) (join_sums term (lo:=627184) (a:=2456) (b:=2456) (join_sums term (lo:=627184) (a:=1228) (b:=1228) (join_sums term (lo:=627184) (a:=614) (b:=614) block627184 block627798) (join_sums term (lo:=628412) (a:=614) (b:=614) block628412 block629026)) (join_sums term (lo:=629640) (a:=1228) (b:=1228) (join_sums term (lo:=629640) (a:=614) (b:=614) block629640 block630254) (join_sums term (lo:=630868) (a:=614) (b:=614) block630868 block631482))) (join_sums term (lo:=632096) (a:=2456) (b:=2457) (join_sums term (lo:=632096) (a:=1228) (b:=1228) (join_sums term (lo:=632096) (a:=614) (b:=614) block632096 block632710) (join_sums term (lo:=633324) (a:=614) (b:=614) block633324 block633938)) (join_sums term (lo:=634552) (a:=1228) (b:=1229) (join_sums term (lo:=634552) (a:=614) (b:=614) block634552 block635166) (join_sums term (lo:=635780) (a:=614) (b:=615) block635780 block636394)))) (join_sums term (lo:=637009) (a:=4913) (b:=4913) (join_sums term (lo:=637009) (a:=2456) (b:=2457) (join_sums term (lo:=637009) (a:=1228) (b:=1228) (join_sums term (lo:=637009) (a:=614) (b:=614) block637009 block637623) (join_sums term (lo:=638237) (a:=614) (b:=614) block638237 block638851)) (join_sums term (lo:=639465) (a:=1228) (b:=1229) (join_sums term (lo:=639465) (a:=614) (b:=614) block639465 block640079) (join_sums term (lo:=640693) (a:=614) (b:=615) block640693 block641307))) (join_sums term (lo:=641922) (a:=2456) (b:=2457) (join_sums term (lo:=641922) (a:=1228) (b:=1228) (join_sums term (lo:=641922) (a:=614) (b:=614) block641922 block642536) (join_sums term (lo:=643150) (a:=614) (b:=614) block643150 block643764)) (join_sums term (lo:=644378) (a:=1228) (b:=1229) (join_sums term (lo:=644378) (a:=614) (b:=614) block644378 block644992) (join_sums term (lo:=645606) (a:=614) (b:=615) block645606 block646220))))) (join_sums term (lo:=646835) (a:=9825) (b:=9826) (join_sums term (lo:=646835) (a:=4912) (b:=4913) (join_sums term (lo:=646835) (a:=2456) (b:=2456) (join_sums term (lo:=646835) (a:=1228) (b:=1228) (join_sums term (lo:=646835) (a:=614) (b:=614) block646835 block647449) (join_sums term (lo:=648063) (a:=614) (b:=614) block648063 block648677)) (join_sums term (lo:=649291) (a:=1228) (b:=1228) (join_sums term (lo:=649291) (a:=614) (b:=614) block649291 block649905) (join_sums term (lo:=650519) (a:=614) (b:=614) block650519 block651133))) (join_sums term (lo:=651747) (a:=2456) (b:=2457) (join_sums term (lo:=651747) (a:=1228) (b:=1228) (join_sums term (lo:=651747) (a:=614) (b:=614) block651747 block652361) (join_sums term (lo:=652975) (a:=614) (b:=614) block652975 block653589)) (join_sums term (lo:=654203) (a:=1228) (b:=1229) (join_sums term (lo:=654203) (a:=614) (b:=614) block654203 block654817) (join_sums term (lo:=655431) (a:=614) (b:=615) block655431 block656045)))) (join_sums term (lo:=656660) (a:=4913) (b:=4913) (join_sums term (lo:=656660) (a:=2456) (b:=2457) (join_sums term (lo:=656660) (a:=1228) (b:=1228) (join_sums term (lo:=656660) (a:=614) (b:=614) block656660 block657274) (join_sums term (lo:=657888) (a:=614) (b:=614) block657888 block658502)) (join_sums term (lo:=659116) (a:=1228) (b:=1229) (join_sums term (lo:=659116) (a:=614) (b:=614) block659116 block659730) (join_sums term (lo:=660344) (a:=614) (b:=615) block660344 block660958))) (join_sums term (lo:=661573) (a:=2456) (b:=2457) (join_sums term (lo:=661573) (a:=1228) (b:=1228) (join_sums term (lo:=661573) (a:=614) (b:=614) block661573 block662187) (join_sums term (lo:=662801) (a:=614) (b:=614) block662801 block663415)) (join_sums term (lo:=664029) (a:=1228) (b:=1229) (join_sums term (lo:=664029) (a:=614) (b:=614) block664029 block664643) (join_sums term (lo:=665257) (a:=614) (b:=615) block665257 block665871))))))) (join_sums term (lo:=666486) (a:=39302) (b:=39302) (join_sums term (lo:=666486) (a:=19651) (b:=19651) (join_sums term (lo:=666486) (a:=9825) (b:=9826) (join_sums term (lo:=666486) (a:=4912) (b:=4913) (join_sums term (lo:=666486) (a:=2456) (b:=2456) (join_sums term (lo:=666486) (a:=1228) (b:=1228) (join_sums term (lo:=666486) (a:=614) (b:=614) block666486 block667100) (join_sums term (lo:=667714) (a:=614) (b:=614) block667714 block668328)) (join_sums term (lo:=668942) (a:=1228) (b:=1228) (join_sums term (lo:=668942) (a:=614) (b:=614) block668942 block669556) (join_sums term (lo:=670170) (a:=614) (b:=614) block670170 block670784))) (join_sums term (lo:=671398) (a:=2456) (b:=2457) (join_sums term (lo:=671398) (a:=1228) (b:=1228) (join_sums term (lo:=671398) (a:=614) (b:=614) block671398 block672012) (join_sums term (lo:=672626) (a:=614) (b:=614) block672626 block673240)) (join_sums term (lo:=673854) (a:=1228) (b:=1229) (join_sums term (lo:=673854) (a:=614) (b:=614) block673854 block674468) (join_sums term (lo:=675082) (a:=614) (b:=615) block675082 block675696)))) (join_sums term (lo:=676311) (a:=4913) (b:=4913) (join_sums term (lo:=676311) (a:=2456) (b:=2457) (join_sums term (lo:=676311) (a:=1228) (b:=1228) (join_sums term (lo:=676311) (a:=614) (b:=614) block676311 block676925) (join_sums term (lo:=677539) (a:=614) (b:=614) block677539 block678153)) (join_sums term (lo:=678767) (a:=1228) (b:=1229) (join_sums term (lo:=678767) (a:=614) (b:=614) block678767 block679381) (join_sums term (lo:=679995) (a:=614) (b:=615) block679995 block680609))) (join_sums term (lo:=681224) (a:=2456) (b:=2457) (join_sums term (lo:=681224) (a:=1228) (b:=1228) (join_sums term (lo:=681224) (a:=614) (b:=614) block681224 block681838) (join_sums term (lo:=682452) (a:=614) (b:=614) block682452 block683066)) (join_sums term (lo:=683680) (a:=1228) (b:=1229) (join_sums term (lo:=683680) (a:=614) (b:=614) block683680 block684294) (join_sums term (lo:=684908) (a:=614) (b:=615) block684908 block685522))))) (join_sums term (lo:=686137) (a:=9825) (b:=9826) (join_sums term (lo:=686137) (a:=4912) (b:=4913) (join_sums term (lo:=686137) (a:=2456) (b:=2456) (join_sums term (lo:=686137) (a:=1228) (b:=1228) (join_sums term (lo:=686137) (a:=614) (b:=614) block686137 block686751) (join_sums term (lo:=687365) (a:=614) (b:=614) block687365 block687979)) (join_sums term (lo:=688593) (a:=1228) (b:=1228) (join_sums term (lo:=688593) (a:=614) (b:=614) block688593 block689207) (join_sums term (lo:=689821) (a:=614) (b:=614) block689821 block690435))) (join_sums term (lo:=691049) (a:=2456) (b:=2457) (join_sums term (lo:=691049) (a:=1228) (b:=1228) (join_sums term (lo:=691049) (a:=614) (b:=614) block691049 block691663) (join_sums term (lo:=692277) (a:=614) (b:=614) block692277 block692891)) (join_sums term (lo:=693505) (a:=1228) (b:=1229) (join_sums term (lo:=693505) (a:=614) (b:=614) block693505 block694119) (join_sums term (lo:=694733) (a:=614) (b:=615) block694733 block695347)))) (join_sums term (lo:=695962) (a:=4913) (b:=4913) (join_sums term (lo:=695962) (a:=2456) (b:=2457) (join_sums term (lo:=695962) (a:=1228) (b:=1228) (join_sums term (lo:=695962) (a:=614) (b:=614) block695962 block696576) (join_sums term (lo:=697190) (a:=614) (b:=614) block697190 block697804)) (join_sums term (lo:=698418) (a:=1228) (b:=1229) (join_sums term (lo:=698418) (a:=614) (b:=614) block698418 block699032) (join_sums term (lo:=699646) (a:=614) (b:=615) block699646 block700260))) (join_sums term (lo:=700875) (a:=2456) (b:=2457) (join_sums term (lo:=700875) (a:=1228) (b:=1228) (join_sums term (lo:=700875) (a:=614) (b:=614) block700875 block701489) (join_sums term (lo:=702103) (a:=614) (b:=614) block702103 block702717)) (join_sums term (lo:=703331) (a:=1228) (b:=1229) (join_sums term (lo:=703331) (a:=614) (b:=614) block703331 block703945) (join_sums term (lo:=704559) (a:=614) (b:=615) block704559 block705173)))))) (join_sums term (lo:=705788) (a:=19651) (b:=19651) (join_sums term (lo:=705788) (a:=9825) (b:=9826) (join_sums term (lo:=705788) (a:=4912) (b:=4913) (join_sums term (lo:=705788) (a:=2456) (b:=2456) (join_sums term (lo:=705788) (a:=1228) (b:=1228) (join_sums term (lo:=705788) (a:=614) (b:=614) block705788 block706402) (join_sums term (lo:=707016) (a:=614) (b:=614) block707016 block707630)) (join_sums term (lo:=708244) (a:=1228) (b:=1228) (join_sums term (lo:=708244) (a:=614) (b:=614) block708244 block708858) (join_sums term (lo:=709472) (a:=614) (b:=614) block709472 block710086))) (join_sums term (lo:=710700) (a:=2456) (b:=2457) (join_sums term (lo:=710700) (a:=1228) (b:=1228) (join_sums term (lo:=710700) (a:=614) (b:=614) block710700 block711314) (join_sums term (lo:=711928) (a:=614) (b:=614) block711928 block712542)) (join_sums term (lo:=713156) (a:=1228) (b:=1229) (join_sums term (lo:=713156) (a:=614) (b:=614) block713156 block713770) (join_sums term (lo:=714384) (a:=614) (b:=615) block714384 block714998)))) (join_sums term (lo:=715613) (a:=4913) (b:=4913) (join_sums term (lo:=715613) (a:=2456) (b:=2457) (join_sums term (lo:=715613) (a:=1228) (b:=1228) (join_sums term (lo:=715613) (a:=614) (b:=614) block715613 block716227) (join_sums term (lo:=716841) (a:=614) (b:=614) block716841 block717455)) (join_sums term (lo:=718069) (a:=1228) (b:=1229) (join_sums term (lo:=718069) (a:=614) (b:=614) block718069 block718683) (join_sums term (lo:=719297) (a:=614) (b:=615) block719297 block719911))) (join_sums term (lo:=720526) (a:=2456) (b:=2457) (join_sums term (lo:=720526) (a:=1228) (b:=1228) (join_sums term (lo:=720526) (a:=614) (b:=614) block720526 block721140) (join_sums term (lo:=721754) (a:=614) (b:=614) block721754 block722368)) (join_sums term (lo:=722982) (a:=1228) (b:=1229) (join_sums term (lo:=722982) (a:=614) (b:=614) block722982 block723596) (join_sums term (lo:=724210) (a:=614) (b:=615) block724210 block724824))))) (join_sums term (lo:=725439) (a:=9825) (b:=9826) (join_sums term (lo:=725439) (a:=4912) (b:=4913) (join_sums term (lo:=725439) (a:=2456) (b:=2456) (join_sums term (lo:=725439) (a:=1228) (b:=1228) (join_sums term (lo:=725439) (a:=614) (b:=614) block725439 block726053) (join_sums term (lo:=726667) (a:=614) (b:=614) block726667 block727281)) (join_sums term (lo:=727895) (a:=1228) (b:=1228) (join_sums term (lo:=727895) (a:=614) (b:=614) block727895 block728509) (join_sums term (lo:=729123) (a:=614) (b:=614) block729123 block729737))) (join_sums term (lo:=730351) (a:=2456) (b:=2457) (join_sums term (lo:=730351) (a:=1228) (b:=1228) (join_sums term (lo:=730351) (a:=614) (b:=614) block730351 block730965) (join_sums term (lo:=731579) (a:=614) (b:=614) block731579 block732193)) (join_sums term (lo:=732807) (a:=1228) (b:=1229) (join_sums term (lo:=732807) (a:=614) (b:=614) block732807 block733421) (join_sums term (lo:=734035) (a:=614) (b:=615) block734035 block734649)))) (join_sums term (lo:=735264) (a:=4913) (b:=4913) (join_sums term (lo:=735264) (a:=2456) (b:=2457) (join_sums term (lo:=735264) (a:=1228) (b:=1228) (join_sums term (lo:=735264) (a:=614) (b:=614) block735264 block735878) (join_sums term (lo:=736492) (a:=614) (b:=614) block736492 block737106)) (join_sums term (lo:=737720) (a:=1228) (b:=1229) (join_sums term (lo:=737720) (a:=614) (b:=614) block737720 block738334) (join_sums term (lo:=738948) (a:=614) (b:=615) block738948 block739562))) (join_sums term (lo:=740177) (a:=2456) (b:=2457) (join_sums term (lo:=740177) (a:=1228) (b:=1228) (join_sums term (lo:=740177) (a:=614) (b:=614) block740177 block740791) (join_sums term (lo:=741405) (a:=614) (b:=614) block741405 block742019)) (join_sums term (lo:=742633) (a:=1228) (b:=1229) (join_sums term (lo:=742633) (a:=614) (b:=614) block742633 block743247) (join_sums term (lo:=743861) (a:=614) (b:=615) block743861 block744475))))))))))

private theorem rows : blockSum term 0 745090 4397030859 :=
  join_sums term (lo:=0) (a:=116264) (b:=628826) before after_cut

theorem exact_upper_sum :
    (∑ p ∈ (Nat.primesLE 745089).filter (116263 < ·),
      (Nat.primeCounting (555157672301/p) - Nat.primeCounting (p-1))) = 4397030859 :=
  right_from_blocks tab prime CheckpointA10425Slim.fast_correct prime_ok (by decide) (by decide) rows

end SharedCorrectionHigh26
