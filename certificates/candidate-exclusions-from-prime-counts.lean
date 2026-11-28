import certificates.«relative-prime-counts-82»

/-!
# Candidate exclusions from the eight endpoint prime counts

Each candidate in the second reduction of OEIS A247824 encodes an index and
slope in the form 32 m + k. The verified local prime-count differences turn
the exact ranks at the eight starting points into exclusions at those indices.
-/
namespace AbsoluteCandidateRanks

def excluded (e : ℕ) : Prop :=
  Nat.primeCounting ((e%32)*(e/32+1322164)-20868473) ≠ e/32

private theorem from_window {e q a rank delta : ℕ}
    (endpoint : (e%32)*(e/32+1322164)-20868473=q)
    (window : Nat.primeCounting q=Nat.primeCounting a+delta)
    (anchor : Nat.primeCounting a=rank)
    (different : rank+delta≠e/32) : excluded e := by
  unfold excluded
  rw [endpoint,window,anchor]
  exact different

private theorem prepend {e : ℕ} {tail : List ℕ}
    (head : excluded e) (rest : ∀ v ∈ tail, excluded v) : ∀ v ∈ e::tail, excluded v := by
  intro v member
  rcases List.mem_cons.mp member with h|h
  · exact h ▸ head
  · exact rest v h

private theorem nil : ∀ v ∈ ([] : List ℕ), excluded v := by simp


private theorem case0 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174075153 :=
  from_window (q:=94085731) (a:=94085731) (rank:=5439846) (delta:=0) rfl WindowRanks.a94085731 at_anchor (by decide)


private theorem case1 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174075345 :=
  from_window (q:=94085833) (a:=94085731) (rank:=5439846) (delta:=7) rfl WindowRanks.a94085833 at_anchor (by decide)


private theorem case2 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174075409 :=
  from_window (q:=94085867) (a:=94085731) (rank:=5439846) (delta:=9) rfl WindowRanks.a94085867 at_anchor (by decide)


private theorem case3 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174076561 :=
  from_window (q:=94086479) (a:=94085731) (rank:=5439846) (delta:=43) rfl WindowRanks.a94086479 at_anchor (by decide)


private theorem case4 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174076689 :=
  from_window (q:=94086547) (a:=94085731) (rank:=5439846) (delta:=49) rfl WindowRanks.a94086547 at_anchor (by decide)


private theorem case5 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174076881 :=
  from_window (q:=94086649) (a:=94085731) (rank:=5439846) (delta:=54) rfl WindowRanks.a94086649 at_anchor (by decide)


private theorem case6 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174076945 :=
  from_window (q:=94086683) (a:=94085731) (rank:=5439846) (delta:=59) rfl WindowRanks.a94086683 at_anchor (by decide)


private theorem case7 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174078993 :=
  from_window (q:=94087771) (a:=94085731) (rank:=5439846) (delta:=118) rfl WindowRanks.a94087771 at_anchor (by decide)


private theorem case8 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174080529 :=
  from_window (q:=94088587) (a:=94085731) (rank:=5439846) (delta:=175) rfl WindowRanks.a94088587 at_anchor (by decide)


private theorem case9 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174081169 :=
  from_window (q:=94088927) (a:=94085731) (rank:=5439846) (delta:=198) rfl WindowRanks.a94088927 at_anchor (by decide)


private theorem case10 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174081361 :=
  from_window (q:=94089029) (a:=94085731) (rank:=5439846) (delta:=206) rfl WindowRanks.a94089029 at_anchor (by decide)


private theorem case11 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174081553 :=
  from_window (q:=94089131) (a:=94085731) (rank:=5439846) (delta:=209) rfl WindowRanks.a94089131 at_anchor (by decide)


private theorem case12 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174081681 :=
  from_window (q:=94089199) (a:=94085731) (rank:=5439846) (delta:=214) rfl WindowRanks.a94089199 at_anchor (by decide)


private theorem case13 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174082449 :=
  from_window (q:=94089607) (a:=94085731) (rank:=5439846) (delta:=235) rfl WindowRanks.a94089607 at_anchor (by decide)


private theorem case14 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174083473 :=
  from_window (q:=94090151) (a:=94085731) (rank:=5439846) (delta:=263) rfl WindowRanks.a94090151 at_anchor (by decide)


private theorem case15 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174083665 :=
  from_window (q:=94090253) (a:=94085731) (rank:=5439846) (delta:=271) rfl WindowRanks.a94090253 at_anchor (by decide)


private theorem case16 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174084241 :=
  from_window (q:=94090559) (a:=94085731) (rank:=5439846) (delta:=289) rfl WindowRanks.a94090559 at_anchor (by decide)


private theorem case17 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174084369 :=
  from_window (q:=94090627) (a:=94085731) (rank:=5439846) (delta:=293) rfl WindowRanks.a94090627 at_anchor (by decide)


private theorem case18 (at_anchor : Nat.primeCounting 94085731=5439846) : excluded 174085201 :=
  from_window (q:=94091069) (a:=94085731) (rank:=5439846) (delta:=317) rfl WindowRanks.a94091069 at_anchor (by decide)


private theorem case19 (at_anchor : Nat.primeCounting 590237761=30841326) : excluded 986922323 :=
  from_window (q:=590237761) (a:=590237761) (rank:=30841326) (delta:=0) rfl WindowRanks.a590237761 at_anchor (by decide)


private theorem case20 (at_anchor : Nat.primeCounting 590237761=30841326) : excluded 986923091 :=
  from_window (q:=590238217) (a:=590237761) (rank:=30841326) (delta:=23) rfl WindowRanks.a590238217 at_anchor (by decide)


private theorem case21 (at_anchor : Nat.primeCounting 590237761=30841326) : excluded 986923987 :=
  from_window (q:=590238749) (a:=590237761) (rank:=30841326) (delta:=52) rfl WindowRanks.a590238749 at_anchor (by decide)


private theorem case22 (at_anchor : Nat.primeCounting 590237761=30841326) : excluded 986924179 :=
  from_window (q:=590238863) (a:=590237761) (rank:=30841326) (delta:=59) rfl WindowRanks.a590238863 at_anchor (by decide)


private theorem case23 (at_anchor : Nat.primeCounting 590237761=30841326) : excluded 986924627 :=
  from_window (q:=590239129) (a:=590237761) (rank:=30841326) (delta:=78) rfl WindowRanks.a590239129 at_anchor (by decide)


private theorem case24 (at_anchor : Nat.primeCounting 590237761=30841326) : excluded 986924947 :=
  from_window (q:=590239319) (a:=590237761) (rank:=30841326) (delta:=90) rfl WindowRanks.a590239319 at_anchor (by decide)


private theorem case25 (at_anchor : Nat.primeCounting 590237761=30841326) : excluded 986926163 :=
  from_window (q:=590240041) (a:=590237761) (rank:=30841326) (delta:=122) rfl WindowRanks.a590240041 at_anchor (by decide)


private theorem case26 (at_anchor : Nat.primeCounting 590237761=30841326) : excluded 986926547 :=
  from_window (q:=590240269) (a:=590237761) (rank:=30841326) (delta:=131) rfl WindowRanks.a590240269 at_anchor (by decide)


private theorem case27 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152523830 :=
  from_window (q:=10425579253) (a:=10425579253) (rank:=473516370) (delta:=0) rfl WindowRanks.a10425579253 at_anchor (by decide)


private theorem case28 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152524150 :=
  from_window (q:=10425579473) (a:=10425579253) (rank:=473516370) (delta:=16) rfl WindowRanks.a10425579473 at_anchor (by decide)


private theorem case29 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152524246 :=
  from_window (q:=10425579539) (a:=10425579253) (rank:=473516370) (delta:=19) rfl WindowRanks.a10425579539 at_anchor (by decide)


private theorem case30 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152524598 :=
  from_window (q:=10425579781) (a:=10425579253) (rank:=473516370) (delta:=29) rfl WindowRanks.a10425579781 at_anchor (by decide)


private theorem case31 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152524630 :=
  from_window (q:=10425579803) (a:=10425579253) (rank:=473516370) (delta:=31) rfl WindowRanks.a10425579803 at_anchor (by decide)


private theorem case32 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152524726 :=
  from_window (q:=10425579869) (a:=10425579253) (rank:=473516370) (delta:=34) rfl WindowRanks.a10425579869 at_anchor (by decide)


private theorem case33 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152525174 :=
  from_window (q:=10425580177) (a:=10425579253) (rank:=473516370) (delta:=49) rfl WindowRanks.a10425580177 at_anchor (by decide)


private theorem case34 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152525494 :=
  from_window (q:=10425580397) (a:=10425579253) (rank:=473516370) (delta:=60) rfl WindowRanks.a10425580397 at_anchor (by decide)


private theorem case35 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152525558 :=
  from_window (q:=10425580441) (a:=10425579253) (rank:=473516370) (delta:=63) rfl WindowRanks.a10425580441 at_anchor (by decide)


private theorem case36 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152526166 :=
  from_window (q:=10425580859) (a:=10425579253) (rank:=473516370) (delta:=75) rfl WindowRanks.a10425580859 at_anchor (by decide)


private theorem case37 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152526326 :=
  from_window (q:=10425580969) (a:=10425579253) (rank:=473516370) (delta:=81) rfl WindowRanks.a10425580969 at_anchor (by decide)


private theorem case38 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152526550 :=
  from_window (q:=10425581123) (a:=10425579253) (rank:=473516370) (delta:=91) rfl WindowRanks.a10425581123 at_anchor (by decide)


private theorem case39 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152526838 :=
  from_window (q:=10425581321) (a:=10425579253) (rank:=473516370) (delta:=102) rfl WindowRanks.a10425581321 at_anchor (by decide)


private theorem case40 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152527094 :=
  from_window (q:=10425581497) (a:=10425579253) (rank:=473516370) (delta:=106) rfl WindowRanks.a10425581497 at_anchor (by decide)


private theorem case41 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152527606 :=
  from_window (q:=10425581849) (a:=10425579253) (rank:=473516370) (delta:=120) rfl WindowRanks.a10425581849 at_anchor (by decide)


private theorem case42 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152528534 :=
  from_window (q:=10425582487) (a:=10425579253) (rank:=473516370) (delta:=147) rfl WindowRanks.a10425582487 at_anchor (by decide)


private theorem case43 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152528566 :=
  from_window (q:=10425582509) (a:=10425579253) (rank:=473516370) (delta:=149) rfl WindowRanks.a10425582509 at_anchor (by decide)


private theorem case44 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152528758 :=
  from_window (q:=10425582641) (a:=10425579253) (rank:=473516370) (delta:=155) rfl WindowRanks.a10425582641 at_anchor (by decide)


private theorem case45 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152529206 :=
  from_window (q:=10425582949) (a:=10425579253) (rank:=473516370) (delta:=172) rfl WindowRanks.a10425582949 at_anchor (by decide)


private theorem case46 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152529238 :=
  from_window (q:=10425582971) (a:=10425579253) (rank:=473516370) (delta:=174) rfl WindowRanks.a10425582971 at_anchor (by decide)


private theorem case47 (at_anchor : Nat.primeCounting 10425579253=473516370) : excluded 15152529590 :=
  from_window (q:=10425583213) (a:=10425579253) (rank:=473516370) (delta:=181) rfl WindowRanks.a10425583213 at_anchor (by decide)


private theorem case48 (at_anchor : Nat.primeCounting 28006150079=1217243858) : excluded 38951803543 :=
  from_window (q:=28006150079) (a:=28006150079) (rank:=1217243858) (delta:=0) rfl WindowRanks.a28006150079 at_anchor (by decide)


private theorem case49 (at_anchor : Nat.primeCounting 204778727327=8190661670) : excluded 262101173401 :=
  from_window (q:=204778727327) (a:=204778727327) (rank:=8190661670) (delta:=0) rfl WindowRanks.a204778727327 at_anchor (by decide)


private theorem case50 (at_anchor : Nat.primeCounting 204778727327=8190661670) : excluded 262101173785 :=
  from_window (q:=204778727627) (a:=204778727327) (rank:=8190661670) (delta:=12) rfl WindowRanks.a204778727627 at_anchor (by decide)


private theorem case51 (at_anchor : Nat.primeCounting 204778727327=8190661670) : excluded 262101173849 :=
  from_window (q:=204778727677) (a:=204778727327) (rank:=8190661670) (delta:=15) rfl WindowRanks.a204778727677 at_anchor (by decide)


private theorem case52 (at_anchor : Nat.primeCounting 204778727327=8190661670) : excluded 262101174233 :=
  from_window (q:=204778727977) (a:=204778727327) (rank:=8190661670) (delta:=28) rfl WindowRanks.a204778727977 at_anchor (by decide)


private theorem case53 (at_anchor : Nat.primeCounting 204778727327=8190661670) : excluded 262101174425 :=
  from_window (q:=204778728127) (a:=204778727327) (rank:=8190661670) (delta:=34) rfl WindowRanks.a204778728127 at_anchor (by decide)


private theorem case54 (at_anchor : Nat.primeCounting 204778727327=8190661670) : excluded 262101175001 :=
  from_window (q:=204778728577) (a:=204778727327) (rank:=8190661670) (delta:=51) rfl WindowRanks.a204778728577 at_anchor (by decide)


private theorem case55 (at_anchor : Nat.primeCounting 204778727327=8190661670) : excluded 262101175129 :=
  from_window (q:=204778728677) (a:=204778727327) (rank:=8190661670) (delta:=56) rfl WindowRanks.a204778728677 at_anchor (by decide)


private theorem case56 (at_anchor : Nat.primeCounting 204778727327=8190661670) : excluded 262101176089 :=
  from_window (q:=204778729427) (a:=204778727327) (rank:=8190661670) (delta:=83) rfl WindowRanks.a204778729427 at_anchor (by decide)


private theorem case57 (at_anchor : Nat.primeCounting 555157672301=21351698638) : excluded 683254356346 :=
  from_window (q:=555157672301) (a:=555157672301) (rank:=21351698638) (delta:=0) rfl WindowRanks.a555157672301 at_anchor (by decide)


private theorem case58 (at_anchor : Nat.primeCounting 555157672301=21351698638) : excluded 683254356858 :=
  from_window (q:=555157672717) (a:=555157672301) (rank:=21351698638) (delta:=18) rfl WindowRanks.a555157672717 at_anchor (by decide)


private theorem case59 (at_anchor : Nat.primeCounting 555157672301=21351698638) : excluded 683254357210 :=
  from_window (q:=555157673003) (a:=555157672301) (rank:=21351698638) (delta:=26) rfl WindowRanks.a555157673003 at_anchor (by decide)


private theorem case60 (at_anchor : Nat.primeCounting 555157672301=21351698638) : excluded 683254357402 :=
  from_window (q:=555157673159) (a:=555157672301) (rank:=21351698638) (delta:=34) rfl WindowRanks.a555157673159 at_anchor (by decide)


private theorem case61 (at_anchor : Nat.primeCounting 555157672301=21351698638) : excluded 683254357498 :=
  from_window (q:=555157673237) (a:=555157672301) (rank:=21351698638) (delta:=36) rfl WindowRanks.a555157673237 at_anchor (by decide)


private theorem case62 (at_anchor : Nat.primeCounting 555157672301=21351698638) : excluded 683254357530 :=
  from_window (q:=555157673263) (a:=555157672301) (rank:=21351698638) (delta:=37) rfl WindowRanks.a555157673263 at_anchor (by decide)


private theorem case63 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439846429 :=
  from_window (q:=11092009835083) (a:=11092009835083) (rank:=382482495196) (delta:=0) rfl WindowRanks.a11092009835083 at_anchor (by decide)


private theorem case64 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439847197 :=
  from_window (q:=11092009835779) (a:=11092009835083) (rank:=382482495196) (delta:=30) rfl WindowRanks.a11092009835779 at_anchor (by decide)


private theorem case65 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439848797 :=
  from_window (q:=11092009837229) (a:=11092009835083) (rank:=382482495196) (delta:=85) rfl WindowRanks.a11092009837229 at_anchor (by decide)


private theorem case66 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439849181 :=
  from_window (q:=11092009837577) (a:=11092009835083) (rank:=382482495196) (delta:=98) rfl WindowRanks.a11092009837577 at_anchor (by decide)


private theorem case67 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439850077 :=
  from_window (q:=11092009838389) (a:=11092009835083) (rank:=382482495196) (delta:=129) rfl WindowRanks.a11092009838389 at_anchor (by decide)


private theorem case68 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439850461 :=
  from_window (q:=11092009838737) (a:=11092009835083) (rank:=382482495196) (delta:=140) rfl WindowRanks.a11092009838737 at_anchor (by decide)


private theorem case69 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439851037 :=
  from_window (q:=11092009839259) (a:=11092009835083) (rank:=382482495196) (delta:=153) rfl WindowRanks.a11092009839259 at_anchor (by decide)


private theorem case70 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439851229 :=
  from_window (q:=11092009839433) (a:=11092009835083) (rank:=382482495196) (delta:=160) rfl WindowRanks.a11092009839433 at_anchor (by decide)


private theorem case71 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439852573 :=
  from_window (q:=11092009840651) (a:=11092009835083) (rank:=382482495196) (delta:=207) rfl WindowRanks.a11092009840651 at_anchor (by decide)


private theorem case72 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439853341 :=
  from_window (q:=11092009841347) (a:=11092009835083) (rank:=382482495196) (delta:=236) rfl WindowRanks.a11092009841347 at_anchor (by decide)


private theorem case73 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439854557 :=
  from_window (q:=11092009842449) (a:=11092009835083) (rank:=382482495196) (delta:=275) rfl WindowRanks.a11092009842449 at_anchor (by decide)


private theorem case74 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439855133 :=
  from_window (q:=11092009842971) (a:=11092009835083) (rank:=382482495196) (delta:=290) rfl WindowRanks.a11092009842971 at_anchor (by decide)


private theorem case75 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439855261 :=
  from_window (q:=11092009843087) (a:=11092009835083) (rank:=382482495196) (delta:=294) rfl WindowRanks.a11092009843087 at_anchor (by decide)


private theorem case76 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439855837 :=
  from_window (q:=11092009843609) (a:=11092009835083) (rank:=382482495196) (delta:=311) rfl WindowRanks.a11092009843609 at_anchor (by decide)


private theorem case77 (at_anchor : Nat.primeCounting 11092009835083=382482495196) : excluded 12239439857821 :=
  from_window (q:=11092009845407) (a:=11092009835083) (rank:=382482495196) (delta:=359) rfl WindowRanks.a11092009845407 at_anchor (by decide)


private theorem case78 (at_anchor : Nat.primeCounting 30110134441897=1003670521508) : excluded 32117456688510 :=
  from_window (q:=30110134441897) (a:=30110134441897) (rank:=1003670521508) (delta:=0) rfl WindowRanks.a30110134441897 at_anchor (by decide)


private theorem case79 (at_anchor : Nat.primeCounting 30110134441897=1003670521508) : excluded 32117456688766 :=
  from_window (q:=30110134442137) (a:=30110134441897) (rank:=1003670521508) (delta:=12) rfl WindowRanks.a30110134442137 at_anchor (by decide)


private theorem case80 (at_anchor : Nat.primeCounting 30110134441897=1003670521508) : excluded 32117456688926 :=
  from_window (q:=30110134442287) (a:=30110134441897) (rank:=1003670521508) (delta:=16) rfl WindowRanks.a30110134442287 at_anchor (by decide)


private theorem case81 (at_anchor : Nat.primeCounting 30110134441897=1003670521508) : excluded 32117456689438 :=
  from_window (q:=30110134442767) (a:=30110134441897) (rank:=1003670521508) (delta:=35) rfl WindowRanks.a30110134442767 at_anchor (by decide)


set_option maxRecDepth 10000 in
theorem first_57
    (h17 : Nat.primeCounting 94085731=5439846)
    (h19 : Nat.primeCounting 590237761=30841326)
    (h22 : Nat.primeCounting 10425579253=473516370)
    (h23 : Nat.primeCounting 28006150079=1217243858)
    (h25 : Nat.primeCounting 204778727327=8190661670) :
    ∀ e ∈ ([174075153,174075345,174075409,174076561,174076689,174076881,174076945,174078993,174080529,174081169,174081361,174081553,174081681,174082449,174083473,174083665,174084241,174084369,174085201,986922323,986923091,986923987,986924179,986924627,986924947,986926163,986926547,15152523830,15152524150,15152524246,15152524598,15152524630,15152524726,15152525174,15152525494,15152525558,15152526166,15152526326,15152526550,15152526838,15152527094,15152527606,15152528534,15152528566,15152528758,15152529206,15152529238,15152529590,38951803543,262101173401,262101173785,262101173849,262101174233,262101174425,262101175001,262101175129,262101176089] : List ℕ), excluded e :=
  (prepend (case0 h17) (prepend (case1 h17) (prepend (case2 h17) (prepend (case3 h17) (prepend (case4 h17) (prepend (case5 h17) (prepend (case6 h17) (prepend (case7 h17) (prepend (case8 h17) (prepend (case9 h17) (prepend (case10 h17) (prepend (case11 h17) (prepend (case12 h17) (prepend (case13 h17) (prepend (case14 h17) (prepend (case15 h17) (prepend (case16 h17) (prepend (case17 h17) (prepend (case18 h17) (prepend (case19 h19) (prepend (case20 h19) (prepend (case21 h19) (prepend (case22 h19) (prepend (case23 h19) (prepend (case24 h19) (prepend (case25 h19) (prepend (case26 h19) (prepend (case27 h22) (prepend (case28 h22) (prepend (case29 h22) (prepend (case30 h22) (prepend (case31 h22) (prepend (case32 h22) (prepend (case33 h22) (prepend (case34 h22) (prepend (case35 h22) (prepend (case36 h22) (prepend (case37 h22) (prepend (case38 h22) (prepend (case39 h22) (prepend (case40 h22) (prepend (case41 h22) (prepend (case42 h22) (prepend (case43 h22) (prepend (case44 h22) (prepend (case45 h22) (prepend (case46 h22) (prepend (case47 h22) (prepend (case48 h23) (prepend (case49 h25) (prepend (case50 h25) (prepend (case51 h25) (prepend (case52 h25) (prepend (case53 h25) (prepend (case54 h25) (prepend (case55 h25) (prepend (case56 h25) nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))


set_option maxRecDepth 10000 in
theorem first_63
    (h17 : Nat.primeCounting 94085731=5439846)
    (h19 : Nat.primeCounting 590237761=30841326)
    (h22 : Nat.primeCounting 10425579253=473516370)
    (h23 : Nat.primeCounting 28006150079=1217243858)
    (h25 : Nat.primeCounting 204778727327=8190661670)
    (h26 : Nat.primeCounting 555157672301=21351698638) :
    ∀ e ∈ ([174075153,174075345,174075409,174076561,174076689,174076881,174076945,174078993,174080529,174081169,174081361,174081553,174081681,174082449,174083473,174083665,174084241,174084369,174085201,986922323,986923091,986923987,986924179,986924627,986924947,986926163,986926547,15152523830,15152524150,15152524246,15152524598,15152524630,15152524726,15152525174,15152525494,15152525558,15152526166,15152526326,15152526550,15152526838,15152527094,15152527606,15152528534,15152528566,15152528758,15152529206,15152529238,15152529590,38951803543,262101173401,262101173785,262101173849,262101174233,262101174425,262101175001,262101175129,262101176089,683254356346,683254356858,683254357210,683254357402,683254357498,683254357530] : List ℕ), excluded e :=
  (prepend (case0 h17) (prepend (case1 h17) (prepend (case2 h17) (prepend (case3 h17) (prepend (case4 h17) (prepend (case5 h17) (prepend (case6 h17) (prepend (case7 h17) (prepend (case8 h17) (prepend (case9 h17) (prepend (case10 h17) (prepend (case11 h17) (prepend (case12 h17) (prepend (case13 h17) (prepend (case14 h17) (prepend (case15 h17) (prepend (case16 h17) (prepend (case17 h17) (prepend (case18 h17) (prepend (case19 h19) (prepend (case20 h19) (prepend (case21 h19) (prepend (case22 h19) (prepend (case23 h19) (prepend (case24 h19) (prepend (case25 h19) (prepend (case26 h19) (prepend (case27 h22) (prepend (case28 h22) (prepend (case29 h22) (prepend (case30 h22) (prepend (case31 h22) (prepend (case32 h22) (prepend (case33 h22) (prepend (case34 h22) (prepend (case35 h22) (prepend (case36 h22) (prepend (case37 h22) (prepend (case38 h22) (prepend (case39 h22) (prepend (case40 h22) (prepend (case41 h22) (prepend (case42 h22) (prepend (case43 h22) (prepend (case44 h22) (prepend (case45 h22) (prepend (case46 h22) (prepend (case47 h22) (prepend (case48 h23) (prepend (case49 h25) (prepend (case50 h25) (prepend (case51 h25) (prepend (case52 h25) (prepend (case53 h25) (prepend (case54 h25) (prepend (case55 h25) (prepend (case56 h25) (prepend (case57 h26) (prepend (case58 h26) (prepend (case59 h26) (prepend (case60 h26) (prepend (case61 h26) (prepend (case62 h26) nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


set_option maxRecDepth 10000 in
theorem first_78
    (h17 : Nat.primeCounting 94085731=5439846)
    (h19 : Nat.primeCounting 590237761=30841326)
    (h22 : Nat.primeCounting 10425579253=473516370)
    (h23 : Nat.primeCounting 28006150079=1217243858)
    (h25 : Nat.primeCounting 204778727327=8190661670)
    (h26 : Nat.primeCounting 555157672301=21351698638)
    (h29 : Nat.primeCounting 11092009835083=382482495196) :
    ∀ e ∈ ([174075153,174075345,174075409,174076561,174076689,174076881,174076945,174078993,174080529,174081169,174081361,174081553,174081681,174082449,174083473,174083665,174084241,174084369,174085201,986922323,986923091,986923987,986924179,986924627,986924947,986926163,986926547,15152523830,15152524150,15152524246,15152524598,15152524630,15152524726,15152525174,15152525494,15152525558,15152526166,15152526326,15152526550,15152526838,15152527094,15152527606,15152528534,15152528566,15152528758,15152529206,15152529238,15152529590,38951803543,262101173401,262101173785,262101173849,262101174233,262101174425,262101175001,262101175129,262101176089,683254356346,683254356858,683254357210,683254357402,683254357498,683254357530,12239439846429,12239439847197,12239439848797,12239439849181,12239439850077,12239439850461,12239439851037,12239439851229,12239439852573,12239439853341,12239439854557,12239439855133,12239439855261,12239439855837,12239439857821] : List ℕ), excluded e :=
  (prepend (case0 h17) (prepend (case1 h17) (prepend (case2 h17) (prepend (case3 h17) (prepend (case4 h17) (prepend (case5 h17) (prepend (case6 h17) (prepend (case7 h17) (prepend (case8 h17) (prepend (case9 h17) (prepend (case10 h17) (prepend (case11 h17) (prepend (case12 h17) (prepend (case13 h17) (prepend (case14 h17) (prepend (case15 h17) (prepend (case16 h17) (prepend (case17 h17) (prepend (case18 h17) (prepend (case19 h19) (prepend (case20 h19) (prepend (case21 h19) (prepend (case22 h19) (prepend (case23 h19) (prepend (case24 h19) (prepend (case25 h19) (prepend (case26 h19) (prepend (case27 h22) (prepend (case28 h22) (prepend (case29 h22) (prepend (case30 h22) (prepend (case31 h22) (prepend (case32 h22) (prepend (case33 h22) (prepend (case34 h22) (prepend (case35 h22) (prepend (case36 h22) (prepend (case37 h22) (prepend (case38 h22) (prepend (case39 h22) (prepend (case40 h22) (prepend (case41 h22) (prepend (case42 h22) (prepend (case43 h22) (prepend (case44 h22) (prepend (case45 h22) (prepend (case46 h22) (prepend (case47 h22) (prepend (case48 h23) (prepend (case49 h25) (prepend (case50 h25) (prepend (case51 h25) (prepend (case52 h25) (prepend (case53 h25) (prepend (case54 h25) (prepend (case55 h25) (prepend (case56 h25) (prepend (case57 h26) (prepend (case58 h26) (prepend (case59 h26) (prepend (case60 h26) (prepend (case61 h26) (prepend (case62 h26) (prepend (case63 h29) (prepend (case64 h29) (prepend (case65 h29) (prepend (case66 h29) (prepend (case67 h29) (prepend (case68 h29) (prepend (case69 h29) (prepend (case70 h29) (prepend (case71 h29) (prepend (case72 h29) (prepend (case73 h29) (prepend (case74 h29) (prepend (case75 h29) (prepend (case76 h29) (prepend (case77 h29) nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


set_option maxRecDepth 10000 in
theorem first_82
    (h17 : Nat.primeCounting 94085731=5439846)
    (h19 : Nat.primeCounting 590237761=30841326)
    (h22 : Nat.primeCounting 10425579253=473516370)
    (h23 : Nat.primeCounting 28006150079=1217243858)
    (h25 : Nat.primeCounting 204778727327=8190661670)
    (h26 : Nat.primeCounting 555157672301=21351698638)
    (h29 : Nat.primeCounting 11092009835083=382482495196)
    (h30 : Nat.primeCounting 30110134441897=1003670521508) :
    ∀ e ∈ ([174075153,174075345,174075409,174076561,174076689,174076881,174076945,174078993,174080529,174081169,174081361,174081553,174081681,174082449,174083473,174083665,174084241,174084369,174085201,986922323,986923091,986923987,986924179,986924627,986924947,986926163,986926547,15152523830,15152524150,15152524246,15152524598,15152524630,15152524726,15152525174,15152525494,15152525558,15152526166,15152526326,15152526550,15152526838,15152527094,15152527606,15152528534,15152528566,15152528758,15152529206,15152529238,15152529590,38951803543,262101173401,262101173785,262101173849,262101174233,262101174425,262101175001,262101175129,262101176089,683254356346,683254356858,683254357210,683254357402,683254357498,683254357530,12239439846429,12239439847197,12239439848797,12239439849181,12239439850077,12239439850461,12239439851037,12239439851229,12239439852573,12239439853341,12239439854557,12239439855133,12239439855261,12239439855837,12239439857821,32117456688510,32117456688766,32117456688926,32117456689438] : List ℕ), excluded e :=
  (prepend (case0 h17) (prepend (case1 h17) (prepend (case2 h17) (prepend (case3 h17) (prepend (case4 h17) (prepend (case5 h17) (prepend (case6 h17) (prepend (case7 h17) (prepend (case8 h17) (prepend (case9 h17) (prepend (case10 h17) (prepend (case11 h17) (prepend (case12 h17) (prepend (case13 h17) (prepend (case14 h17) (prepend (case15 h17) (prepend (case16 h17) (prepend (case17 h17) (prepend (case18 h17) (prepend (case19 h19) (prepend (case20 h19) (prepend (case21 h19) (prepend (case22 h19) (prepend (case23 h19) (prepend (case24 h19) (prepend (case25 h19) (prepend (case26 h19) (prepend (case27 h22) (prepend (case28 h22) (prepend (case29 h22) (prepend (case30 h22) (prepend (case31 h22) (prepend (case32 h22) (prepend (case33 h22) (prepend (case34 h22) (prepend (case35 h22) (prepend (case36 h22) (prepend (case37 h22) (prepend (case38 h22) (prepend (case39 h22) (prepend (case40 h22) (prepend (case41 h22) (prepend (case42 h22) (prepend (case43 h22) (prepend (case44 h22) (prepend (case45 h22) (prepend (case46 h22) (prepend (case47 h22) (prepend (case48 h23) (prepend (case49 h25) (prepend (case50 h25) (prepend (case51 h25) (prepend (case52 h25) (prepend (case53 h25) (prepend (case54 h25) (prepend (case55 h25) (prepend (case56 h25) (prepend (case57 h26) (prepend (case58 h26) (prepend (case59 h26) (prepend (case60 h26) (prepend (case61 h26) (prepend (case62 h26) (prepend (case63 h29) (prepend (case64 h29) (prepend (case65 h29) (prepend (case66 h29) (prepend (case67 h29) (prepend (case68 h29) (prepend (case69 h29) (prepend (case70 h29) (prepend (case71 h29) (prepend (case72 h29) (prepend (case73 h29) (prepend (case74 h29) (prepend (case75 h29) (prepend (case76 h29) (prepend (case77 h29) (prepend (case78 h30) (prepend (case79 h30) (prepend (case80 h30) (prepend (case81 h30) nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end AbsoluteCandidateRanks
