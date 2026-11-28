import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 17, 18, 19, 20. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x17 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000010000000700000003)
  | ⟨false,false,true⟩ => (-96,0x3000000070000000100000001)
  | ⟨false,true,false⟩ => (-1,0x2000000020000000380000003)
  | ⟨false,true,true⟩ => (-96,0x180000001c000000100000001)
  | ⟨true,false,false⟩ => (0,0x2000000030000000f)
  | ⟨true,false,true⟩ => (-63,0x78000000180000001)
  | ⟨true,true,false⟩ => (-3,0x40000000c0000000f)
  | ⟨true,true,true⟩ => (-65,0x3c000000300000001)

set_option maxRecDepth 20000 in
private theorem view7x17 (g : Orientation) : cache7x17 g=views (shape 7 17) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x17x0 : RowFact 7 17 ⟨false,false,false⟩ :=
  checked_row (mask:=0x1800000024000000620000008200000082000000820000008c0000004800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x17 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x17x1 : RowFact 7 17 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000280000006c000000820000008200000082000000820000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x17 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x17x2 : RowFact 7 17 ⟨false,true,false⟩ :=
  checked_row (mask:=0x300000004800000088000001080000020800000108000000880000004800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x17 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x17x3 : RowFact 7 17 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000002800000068000000880000018800000208000001080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x17 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x17x4 : RowFact 7 17 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e0000002100000061000000810000008100000046000000240000001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x17 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x17x5 : RowFact 7 17 ⟨true,false,true⟩ :=
  checked_row (mask:=0x80000001400000026000000410000008100000081000000410000003e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x17 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x17x6 : RowFact 7 17 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf00000010800000308000004080000020800000108000000900000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x17 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x17x7 : RowFact 7 17 ⟨true,true,true⟩ :=
  checked_row (mask:=0x2000000050000000c800000108000003080000040800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x17 (by decide +kernel) (by decide +kernel)

theorem checked7x17 (g : Orientation) : RowFact 7 17 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x17x0
  · exact part7x17x1
  · exact part7x17x2
  · exact part7x17x3
  · exact part7x17x4
  · exact part7x17x5
  · exact part7x17x6
  · exact part7x17x7

private def cache7x18 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000030000000100000007)
  | ⟨false,false,true⟩ => (-96,0x7000000010000000300000001)
  | ⟨false,true,false⟩ => (-2,0x4000000060000000400000007)
  | ⟨false,true,true⟩ => (-96,0x1c00000010000000180000001)
  | ⟨true,false,false⟩ => (0,0x1000000050000000f)
  | ⟨true,false,true⟩ => (-64,0xf0000000500000001)
  | ⟨true,true,false⟩ => (-3,0x80000000a0000000f)
  | ⟨true,true,true⟩ => (-64,0x1e000000140000001)

set_option maxRecDepth 20000 in
private theorem view7x18 (g : Orientation) : cache7x18 g=views (shape 7 18) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x18x0 : RowFact 7 18 ⟨false,false,false⟩ :=
  checked_row (mask:=0x1c0000002200000042000000420000008200000084000000840000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x18 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x18x1 : RowFact 7 18 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000280000004400000044000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x18 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x18x2 : RowFact 7 18 ⟨false,true,false⟩ :=
  checked_row (mask:=0x700000008800000108000001880000020800000188000001080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x18 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x18x3 : RowFact 7 18 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1000000028000000480000008800000088000001080000018800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x18 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x18x4 : RowFact 7 18 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e00000021000000410000004100000081000000820000008c0000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x18 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x18x5 : RowFact 7 18 ⟨true,false,true⟩ :=
  checked_row (mask:=0x100000002c0000004a000000410000008100000081000000810000007e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x18 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x18x6 : RowFact 7 18 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf00000010800000208000003080000040800000208000001880000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x18 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x18x7 : RowFact 7 18 ⟨true,true,true⟩ :=
  checked_row (mask:=0x10000000680000008800000108000002080000020800000408000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x18 (by decide +kernel) (by decide +kernel)

theorem checked7x18 (g : Orientation) : RowFact 7 18 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x18x0
  · exact part7x18x1
  · exact part7x18x2
  · exact part7x18x3
  · exact part7x18x4
  · exact part7x18x5
  · exact part7x18x6
  · exact part7x18x7

private def cache7x19 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000070000000100000003)
  | ⟨false,false,true⟩ => (-96,0x3000000010000000700000001)
  | ⟨false,true,false⟩ => (-1,0x2000000038000000200000003)
  | ⟨false,true,true⟩ => (-96,0x18000000100000001c0000001)
  | ⟨true,false,false⟩ => (0,0x4000000050000000f)
  | ⟨true,false,true⟩ => (-62,0x3c000000140000001)
  | ⟨true,true,false⟩ => (-3,0x20000000a0000000f)
  | ⟨true,true,true⟩ => (-66,0x78000000500000001)

set_option maxRecDepth 20000 in
private theorem view7x19 (g : Orientation) : cache7x19 g=views (shape 7 19) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x19x0 : RowFact 7 19 ⟨false,false,false⟩ :=
  checked_row (mask:=0x180000006400000084000000820000008200000082000000420000004c00000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x19 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x19x1 : RowFact 7 19 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c00000082000000820000008200000082000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x19 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x19x2 : RowFact 7 19 ⟨false,true,false⟩ :=
  checked_row (mask:=0x30000000c80000010800000188000002080000018800000108000000c800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x19 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x19x3 : RowFact 7 19 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000006800000188000002080000018800000108000000c80000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x19 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x19x4 : RowFact 7 19 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e0000006100000081000000810000004100000042000000320000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x19 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x19x5 : RowFact 7 19 ⟨true,false,true⟩ :=
  checked_row (mask:=0x40000001a00000062000000810000008100000041000000410000003e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x19 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x19x6 : RowFact 7 19 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf0000003080000040800000208000002080000010800000130000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x19 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x19x7 : RowFact 7 19 ⟨true,true,true⟩ :=
  checked_row (mask:=0x40000001b00000022800000208000004080000030800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x19 (by decide +kernel) (by decide +kernel)

theorem checked7x19 (g : Orientation) : RowFact 7 19 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x19x0
  · exact part7x19x1
  · exact part7x19x2
  · exact part7x19x3
  · exact part7x19x4
  · exact part7x19x5
  · exact part7x19x6
  · exact part7x19x7

private def cache7x20 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x200000003000000010000000100000003)
  | ⟨false,false,true⟩ => (-127,0x180000000800000008000000180000001)
  | ⟨false,true,false⟩ => (-1,0x100000003000000020000000200000003)
  | ⟨false,true,true⟩ => (-129,0x300000002000000020000000300000001)
  | ⟨true,false,false⟩ => (0,0x190000000f)
  | ⟨true,false,true⟩ => (-32,0xf00000019)
  | ⟨true,true,false⟩ => (-3,0x98000000f)
  | ⟨true,true,true⟩ => (-36,0x1e00000013)

set_option maxRecDepth 20000 in
private theorem view7x20 (g : Orientation) : cache7x20 g=views (shape 7 20) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x20x0 : RowFact 7 20 ⟨false,false,false⟩ :=
  checked_row (mask:=0x30000000480000004400000044000000440000004400000044000000440000004400000024000000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x20 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x20x1 : RowFact 7 20 ⟨false,false,true⟩ :=
  checked_row (mask:=0x1000000028000000440000004400000044000000440000004400000044000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x20 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x20x2 : RowFact 7 20 ⟨false,true,false⟩ :=
  checked_row (mask:=0x60000000900000008800000048000000880000008800000088000000480000008800000090000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x20 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x20x3 : RowFact 7 20 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a0000000900000008800000048000000880000008800000048000000480000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x20 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x20x4 : RowFact 7 20 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3c000000420000004100000040800000208000004080000048800000370000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x20 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x20x5 : RowFact 7 20 ⟨true,false,true⟩ :=
  checked_row (mask:=0x260000005900000040800000408000002080000040800000410000003e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x20 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x20x6 : RowFact 7 20 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1e0000002100000040800000408000002080000020800000448000003b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x20 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x20x7 : RowFact 7 20 ⟨true,true,true⟩ :=
  checked_row (mask:=0x320000004d00000040800000208000002080000040800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x20 (by decide +kernel) (by decide +kernel)

theorem checked7x20 (g : Orientation) : RowFact 7 20 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x20x0
  · exact part7x20x1
  · exact part7x20x2
  · exact part7x20x3
  · exact part7x20x4
  · exact part7x20x5
  · exact part7x20x6
  · exact part7x20x7

end HalfIndexRows
