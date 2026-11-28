import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 21, 22, 23, 24. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x21 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x3000000010000000100000007)
  | ⟨false,false,true⟩ => (-96,0x7000000010000000100000003)
  | ⟨false,true,false⟩ => (-2,0x6000000040000000400000007)
  | ⟨false,true,true⟩ => (-97,0x3800000020000000200000003)
  | ⟨true,false,false⟩ => (0,0x1000000090000000f)
  | ⟨true,false,true⟩ => (-64,0xf0000000900000001)
  | ⟨true,true,false⟩ => (-3,0x8000000090000000f)
  | ⟨true,true,true⟩ => (-64,0x1e000000120000001)

set_option maxRecDepth 20000 in
private theorem view7x21 (g : Orientation) : cache7x21 g=views (shape 7 21) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x21x0 : RowFact 7 21 ⟨false,false,false⟩ :=
  checked_row (mask:=0x3c0000004200000042000000420000008200000084000000840000008400000078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x21 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x21x1 : RowFact 7 21 ⟨false,false,true⟩ :=
  checked_row (mask:=0x38000000440000004400000044000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x21 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x21x2 : RowFact 7 21 ⟨false,true,false⟩ :=
  checked_row (mask:=0xf000000108000000880000018800000208000001880000008800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x21 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x21x3 : RowFact 7 21 ⟨false,true,true⟩ :=
  checked_row (mask:=0x700000008800000048000000c800000108000000880000018800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x21 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x21x4 : RowFact 7 21 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3e00000041000000410000004100000081000000810000008e0000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x21 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x21x5 : RowFact 7 21 ⟨true,false,true⟩ :=
  checked_row (mask:=0x300000004e00000049000000410000008100000081000000810000007e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x21 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x21x6 : RowFact 7 21 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1f00000020800000208000003080000040800000408000003880000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x21 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x21x7 : RowFact 7 21 ⟨true,true,true⟩ :=
  checked_row (mask:=0x30000001c80000024800000208000003080000040800000408000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x21 (by decide +kernel) (by decide +kernel)

theorem checked7x21 (g : Orientation) : RowFact 7 21 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x21x0
  · exact part7x21x1
  · exact part7x21x2
  · exact part7x21x3
  · exact part7x21x4
  · exact part7x21x5
  · exact part7x21x6
  · exact part7x21x7

private def cache7x22 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000010000000500000007)
  | ⟨false,false,true⟩ => (-96,0x7000000050000000100000001)
  | ⟨false,true,false⟩ => (-2,0x4000000040000000500000007)
  | ⟨false,true,true⟩ => (-96,0x1c00000014000000100000001)
  | ⟨true,false,false⟩ => (0,0x3000000010000000f)
  | ⟨true,false,true⟩ => (-64,0xf0000000100000003)
  | ⟨true,true,false⟩ => (-3,0xc000000080000000f)
  | ⟨true,true,true⟩ => (-65,0x3c000000200000003)

set_option maxRecDepth 20000 in
private theorem view7x22 (g : Orientation) : cache7x22 g=views (shape 7 22) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x22x0 : RowFact 7 22 ⟨false,false,false⟩ :=
  checked_row (mask:=0x1c00000022000000620000008200000082000000820000008c0000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x22 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x22x1 : RowFact 7 22 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000280000006c000000aa000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x22 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x22x2 : RowFact 7 22 ⟨false,true,false⟩ :=
  checked_row (mask:=0x700000008800000188000002080000020800000208000001880000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x22 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x22x3 : RowFact 7 22 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000002800000068000000a800000188000002880000020800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x22 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x22x4 : RowFact 7 22 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e0000002100000061000000810000008100000086000000840000007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x22 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x22x5 : RowFact 7 22 ⟨true,false,true⟩ :=
  checked_row (mask:=0x180000002400000066000000810000008100000081000000810000007e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x22 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x22x6 : RowFact 7 22 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf0000001080000030800000408000004080000030800000108000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x22 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x22x7 : RowFact 7 22 ⟨true,true,true⟩ :=
  checked_row (mask:=0x3000000048000000c800000108000003080000040800000408000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x22 (by decide +kernel) (by decide +kernel)

theorem checked7x22 (g : Orientation) : RowFact 7 22 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x22x0
  · exact part7x22x1
  · exact part7x22x2
  · exact part7x22x3
  · exact part7x22x4
  · exact part7x22x5
  · exact part7x22x6
  · exact part7x22x7

private def cache7x23 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x100000001000000010000000f)
  | ⟨false,false,true⟩ => (-96,0xf000000010000000100000001)
  | ⟨false,true,false⟩ => (-3,0x800000008000000080000000f)
  | ⟨false,true,true⟩ => (-96,0x1e00000010000000100000001)
  | ⟨true,false,false⟩ => (0,0x100000001000000010000000f)
  | ⟨true,false,true⟩ => (-96,0xf000000010000000100000001)
  | ⟨true,true,false⟩ => (-3,0x800000008000000080000000f)
  | ⟨true,true,true⟩ => (-96,0x1e00000010000000100000001)

set_option maxRecDepth 20000 in
private theorem view7x23 (g : Orientation) : cache7x23 g=views (shape 7 23) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x23x0 : RowFact 7 23 ⟨false,false,false⟩ :=
  checked_row (mask:=0x1e0000002100000021000000e1000001010000010e0000010800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x23 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x23x1 : RowFact 7 23 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000028000000ee00000101000001010000010100000101000000fe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x23 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x23x2 : RowFact 7 23 ⟨false,true,false⟩ :=
  checked_row (mask:=0xf000000108000001080000070800000808000007080000010800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x23 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x23x3 : RowFact 7 23 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000002800000028000000e800000108000001080000070800000808000007f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x23 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x23x4 : RowFact 7 23 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e0000002100000021000000e1000001010000010e0000010800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x23 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x23x5 : RowFact 7 23 ⟨true,false,true⟩ :=
  checked_row (mask:=0x100000002800000028000000ee00000101000001010000010100000101000000fe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x23 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x23x6 : RowFact 7 23 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf000000108000001080000070800000808000007080000010800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x23 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x23x7 : RowFact 7 23 ⟨true,true,true⟩ :=
  checked_row (mask:=0x100000002800000028000000e800000108000001080000070800000808000007f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x23 (by decide +kernel) (by decide +kernel)

theorem checked7x23 (g : Orientation) : RowFact 7 23 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x23x0
  · exact part7x23x1
  · exact part7x23x2
  · exact part7x23x3
  · exact part7x23x4
  · exact part7x23x5
  · exact part7x23x6
  · exact part7x23x7

private def cache7x24 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000030000000700000001)
  | ⟨false,false,true⟩ => (-96,0x1000000070000000300000001)
  | ⟨false,true,false⟩ => (0,0x10000000180000001c0000001)
  | ⟨false,true,true⟩ => (-96,0x100000001c000000180000001)
  | ⟨true,false,false⟩ => (0,0x2000000060000000f)
  | ⟨true,false,true⟩ => (-63,0x78000000300000001)
  | ⟨true,true,false⟩ => (-3,0x4000000060000000f)
  | ⟨true,true,true⟩ => (-65,0x3c000000180000001)

set_option maxRecDepth 20000 in
private theorem view7x24 (g : Orientation) : cache7x24 g=views (shape 7 24) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x24x0 : RowFact 7 24 ⟨false,false,false⟩ :=
  checked_row (mask:=0x100000002c00000042000000820000008200000082000000840000006800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x24 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x24x1 : RowFact 7 24 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000820000008200000082000000820000006c00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x24 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x24x2 : RowFact 7 24 ⟨false,true,false⟩ :=
  checked_row (mask:=0x100000006800000088000001080000020800000108000000880000006800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x24 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x24x3 : RowFact 7 24 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000002800000048000000880000010800000208000001880000006800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x24 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x24x4 : RowFact 7 24 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e0000002100000041000000810000004100000042000000340000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x24 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x24x5 : RowFact 7 24 ⟨true,false,true⟩ :=
  checked_row (mask:=0x80000001400000022000000410000004100000081000000610000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x24 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x24x6 : RowFact 7 24 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf00000010800000208000004080000020800000110000000d00000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x24 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x24x7 : RowFact 7 24 ⟨true,true,true⟩ :=
  checked_row (mask:=0x20000000500000009000000108000002080000040800000308000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x24 (by decide +kernel) (by decide +kernel)

theorem checked7x24 (g : Orientation) : RowFact 7 24 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x24x0
  · exact part7x24x1
  · exact part7x24x2
  · exact part7x24x3
  · exact part7x24x4
  · exact part7x24x5
  · exact part7x24x6
  · exact part7x24x7

end HalfIndexRows
