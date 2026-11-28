import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 13, 14, 15, 16. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x13 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x20000000300000001000000010000000100000001)
  | ⟨false,false,true⟩ => (-159,0x8000000080000000800000008000000180000001)
  | ⟨false,true,false⟩ => (0,0x8000000180000001000000010000000100000001)
  | ⟨false,true,true⟩ => (-161,0x20000000200000002000000020000000300000001)
  | ⟨true,false,false⟩ => (0,0x300000001f)
  | ⟨true,false,true⟩ => (-28,0x1f0000003)
  | ⟨true,true,false⟩ => (-4,0x18000001f)
  | ⟨true,true,true⟩ => (-37,0x3e00000003)

set_option maxRecDepth 20000 in
private theorem view7x13 (g : Orientation) : cache7x13 g=views (shape 7 13) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x13x0 : RowFact 7 13 ⟨false,false,false⟩ :=
  checked_row (mask:=0x2000000050000000480000004800000048000000480000004400000024000000240000002400000024000000140000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x13 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x13x1 : RowFact 7 13 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000280000004400000044000000440000004400000044000000440000002800000028000000280000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x13 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x13x2 : RowFact 7 13 ⟨false,true,false⟩ :=
  checked_row (mask:=0x2000000050000000480000004800000048000000880000008800000088000000480000004800000048000000500000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x13 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x13x3 : RowFact 7 13 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a00000009000000088000000480000004800000048000000480000002800000028000000280000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x13 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x13x4 : RowFact 7 13 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3e0000004100000040800000204000002040000020400000204000001e400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x13 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x13x5 : RowFact 7 13 ⟨true,false,true⟩ :=
  checked_row (mask:=0x30000003c8000004040000040400000204000002040000020400000208000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x13 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x13x6 : RowFact 7 13 ⟨true,true,false⟩ :=
  checked_row (mask:=0x3e0000004100000080800000808000004080000040800000408000004f0000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x13 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x13x7 : RowFact 7 13 ⟨true,true,true⟩ :=
  checked_row (mask:=0x600000009e0000008100000040800000408000004080000040800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x13 (by decide +kernel) (by decide +kernel)

theorem checked7x13 (g : Orientation) : RowFact 7 13 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x13x0
  · exact part7x13x1
  · exact part7x13x2
  · exact part7x13x3
  · exact part7x13x4
  · exact part7x13x5
  · exact part7x13x6
  · exact part7x13x7

private def cache7x14 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000030000000300000003)
  | ⟨false,false,true⟩ => (-96,0x3000000030000000300000001)
  | ⟨false,true,false⟩ => (-1,0x2000000030000000300000003)
  | ⟨false,true,true⟩ => (-96,0x1800000018000000180000001)
  | ⟨true,false,false⟩ => (0,0x70000000f)
  | ⟨true,false,true⟩ => (-32,0xf00000007)
  | ⟨true,true,false⟩ => (-3,0xe0000000f)
  | ⟨true,true,true⟩ => (-34,0x780000007)

set_option maxRecDepth 20000 in
private theorem view7x14 (g : Orientation) : cache7x14 g=views (shape 7 14) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x14x0 : RowFact 7 14 ⟨false,false,false⟩ :=
  checked_row (mask:=0x180000002400000044000000440000004400000044000000440000004800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x14 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x14x1 : RowFact 7 14 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000440000004400000044000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x14 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x14x2 : RowFact 7 14 ⟨false,true,false⟩ :=
  checked_row (mask:=0x300000004800000088000000880000008800000088000000880000004800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x14 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x14x3 : RowFact 7 14 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000002800000048000000880000008800000088000000880000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x14 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x14x4 : RowFact 7 14 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e00000021000000410000004100000041000000420000003c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x14 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x14x5 : RowFact 7 14 ⟨true,false,true⟩ :=
  checked_row (mask:=0x1c00000022000000410000004100000041000000410000003e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x14 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x14x6 : RowFact 7 14 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf00000010800000208000002080000020800000108000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x14 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x14x7 : RowFact 7 14 ⟨true,true,true⟩ :=
  checked_row (mask:=0x700000008800000108000002080000020800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x14 (by decide +kernel) (by decide +kernel)

theorem checked7x14 (g : Orientation) : RowFact 7 14 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x14x0
  · exact part7x14x1
  · exact part7x14x2
  · exact part7x14x3
  · exact part7x14x4
  · exact part7x14x5
  · exact part7x14x6
  · exact part7x14x7

private def cache7x15 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x3000000010000000300000003)
  | ⟨false,false,true⟩ => (-96,0x3000000030000000100000003)
  | ⟨false,true,false⟩ => (-1,0x3000000020000000300000003)
  | ⟨false,true,true⟩ => (-97,0x3000000030000000200000003)
  | ⟨true,false,false⟩ => (0,0xb0000000f)
  | ⟨true,false,true⟩ => (-32,0xf0000000b)
  | ⟨true,true,false⟩ => (-3,0xd0000000f)
  | ⟨true,true,true⟩ => (-35,0xf0000000d)

set_option maxRecDepth 20000 in
private theorem view7x15 (g : Orientation) : cache7x15 g=views (shape 7 15) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x15x0 : RowFact 7 15 ⟨false,false,false⟩ :=
  checked_row (mask:=0x380000004400000044000000440000004400000044000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x15 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x15x1 : RowFact 7 15 ⟨false,false,true⟩ :=
  checked_row (mask:=0x380000004400000044000000440000004400000044000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x15 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x15x2 : RowFact 7 15 ⟨false,true,false⟩ :=
  checked_row (mask:=0x700000008800000088000000880000008800000088000000880000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x15 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x15x3 : RowFact 7 15 ⟨false,true,true⟩ :=
  checked_row (mask:=0x700000008800000048000000880000008800000088000000880000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x15 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x15x4 : RowFact 7 15 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3e00000041000000410000004100000041000000410000003e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x15 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x15x5 : RowFact 7 15 ⟨true,false,true⟩ :=
  checked_row (mask:=0x3e00000041000000410000004100000041000000410000003e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x15 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x15x6 : RowFact 7 15 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1f00000020800000208000002080000020800000208000001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x15 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x15x7 : RowFact 7 15 ⟨true,true,true⟩ :=
  checked_row (mask:=0x1f00000020800000208000002080000020800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x15 (by decide +kernel) (by decide +kernel)

theorem checked7x15 (g : Orientation) : RowFact 7 15 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x15x0
  · exact part7x15x1
  · exact part7x15x2
  · exact part7x15x3
  · exact part7x15x4
  · exact part7x15x5
  · exact part7x15x6
  · exact part7x15x7

private def cache7x16 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000010000000300000007)
  | ⟨false,false,true⟩ => (-96,0x7000000030000000100000001)
  | ⟨false,true,false⟩ => (-2,0x4000000040000000600000007)
  | ⟨false,true,true⟩ => (-96,0x1c00000018000000100000001)
  | ⟨true,false,false⟩ => (0,0x1000000030000000f)
  | ⟨true,false,true⟩ => (-64,0xf0000000300000001)
  | ⟨true,true,false⟩ => (-3,0x80000000c0000000f)
  | ⟨true,true,true⟩ => (-64,0x1e000000180000001)

set_option maxRecDepth 20000 in
private theorem view7x16 (g : Orientation) : cache7x16 g=views (shape 7 16) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x16x0 : RowFact 7 16 ⟨false,false,false⟩ :=
  checked_row (mask:=0x1c0000002200000022000000420000008200000084000000880000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x16 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x16x1 : RowFact 7 16 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000280000002800000044000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x16 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x16x2 : RowFact 7 16 ⟨false,true,false⟩ :=
  checked_row (mask:=0x700000008800000088000001080000020800000108000000880000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x16 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x16x3 : RowFact 7 16 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1000000028000000280000004800000088000000880000010800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x16 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x16x4 : RowFact 7 16 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e0000002100000021000000410000008100000086000000880000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x16 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x16x5 : RowFact 7 16 ⟨true,false,true⟩ :=
  checked_row (mask:=0x100000002800000026000000410000008100000081000000810000007e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x16 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x16x6 : RowFact 7 16 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf00000010800000108000002080000040800000308000000880000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x16 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x16x7 : RowFact 7 16 ⟨true,true,true⟩ :=
  checked_row (mask:=0x1000000028000000c800000108000001080000020800000408000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x16 (by decide +kernel) (by decide +kernel)

theorem checked7x16 (g : Orientation) : RowFact 7 16 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x16x0
  · exact part7x16x1
  · exact part7x16x2
  · exact part7x16x3
  · exact part7x16x4
  · exact part7x16x5
  · exact part7x16x6
  · exact part7x16x7

end HalfIndexRows
