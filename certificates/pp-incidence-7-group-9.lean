import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 33, 34, 35, 36. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x33 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x400000007000000010000000100000001)
  | ⟨false,false,true⟩ => (-126,0x400000004000000040000001c0000001)
  | ⟨false,true,false⟩ => (0,0x40000001c00000010000000100000001)
  | ⟨false,true,true⟩ => (-130,0x400000004000000040000000700000001)
  | ⟨true,false,false⟩ => (0,0x18000000080000000f)
  | ⟨true,false,true⟩ => (-61,0x1e000000100000003)
  | ⟨true,true,false⟩ => (-3,0x1800000010000000f)
  | ⟨true,true,true⟩ => (-68,0x1e0000000200000003)

set_option maxRecDepth 20000 in
private theorem view7x33 (g : Orientation) : cache7x33 g=views (shape 7 33) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x33x0 : RowFact 7 33 ⟨false,false,false⟩ :=
  checked_row (mask:=0x40000000b000000088000000880000008c000000820000006200000022000000220000001a000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x33 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x33x1 : RowFact 7 33 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c00000082000000820000008200000082000000820000006c000000280000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x33 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x33x2 : RowFact 7 33 ⟨false,true,false⟩ :=
  checked_row (mask:=0x40000000b000000088000001880000020800000208000002080000018800000088000000b0000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x33 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x33x3 : RowFact 7 33 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000002c0000002300000020800000188000000880000008800000068000000280000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x33 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x33x4 : RowFact 7 33 ⟨true,false,false⟩ :=
  checked_row (mask:=0x7800000086000000810000006100000020800000208000001c800000048000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x33 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x33x5 : RowFact 7 33 ⟨true,false,true⟩ :=
  checked_row (mask:=0xc000000130000007080000080800000808000006080000021000000210000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x33 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x33x6 : RowFact 7 33 ⟨true,true,false⟩ :=
  checked_row (mask:=0x3c0000004300000040800000808000008080000060800000270000002400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x33 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x33x7 : RowFact 7 33 ⟨true,true,true⟩ :=
  checked_row (mask:=0x60000000980000008400000043000000408000002080000010800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x33 (by decide +kernel) (by decide +kernel)

theorem checked7x33 (g : Orientation) : RowFact 7 33 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x33x0
  · exact part7x33x1
  · exact part7x33x2
  · exact part7x33x3
  · exact part7x33x4
  · exact part7x33x5
  · exact part7x33x6
  · exact part7x33x7

private def cache7x34 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x300000002000000030000000100000001)
  | ⟨false,false,true⟩ => (-128,0x100000001000000030000000200000003)
  | ⟨false,true,false⟩ => (0,0x180000000800000018000000100000001)
  | ⟨false,true,true⟩ => (-129,0x200000002000000030000000100000003)
  | ⟨true,false,false⟩ => (0,0x1c00000017)
  | ⟨true,false,true⟩ => (-30,0x5c0000007)
  | ⟨true,true,false⟩ => (-4,0x70000001d)
  | ⟨true,true,true⟩ => (-36,0x1d00000007)

set_option maxRecDepth 20000 in
private theorem view7x34 (g : Orientation) : cache7x34 g=views (shape 7 34) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x34x0 : RowFact 7 34 ⟨false,false,false⟩ :=
  checked_row (mask:=0x30000000480000004800000044000000440000004400000044000000440000002400000024000000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x34 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x34x1 : RowFact 7 34 ⟨false,false,true⟩ :=
  checked_row (mask:=0x3800000044000000440000004400000044000000440000004400000044000000280000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x34 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x34x2 : RowFact 7 34 ⟨false,true,false⟩ :=
  checked_row (mask:=0x30000000480000004800000088000000880000008800000088000000880000004800000048000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x34 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x34x3 : RowFact 7 34 ⟨false,true,true⟩ :=
  checked_row (mask:=0x7000000088000000900000008800000088000000880000004800000048000000280000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x34 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x34x4 : RowFact 7 34 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3f000000408000004080000040800000208000002080000018800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x34 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x34x5 : RowFact 7 34 ⟨true,false,true⟩ :=
  checked_row (mask:=0xf0000003080000040800000408000004080000020800000228000001d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x34 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x34x6 : RowFact 7 34 ⟨true,true,false⟩ :=
  checked_row (mask:=0x3f0000004080000041000000408000004080000020800000230000001c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x34 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x34x7 : RowFact 7 34 ⟨true,true,true⟩ :=
  checked_row (mask:=0x3c000000430000004080000041000000408000002080000028800000170000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x34 (by decide +kernel) (by decide +kernel)

theorem checked7x34 (g : Orientation) : RowFact 7 34 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x34x0
  · exact part7x34x1
  · exact part7x34x2
  · exact part7x34x3
  · exact part7x34x4
  · exact part7x34x5
  · exact part7x34x6
  · exact part7x34x7

private def cache7x35 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x30000000300000007)
  | ⟨false,false,true⟩ => (-64,0x70000000300000003)
  | ⟨false,true,false⟩ => (-2,0x60000000600000007)
  | ⟨false,true,true⟩ => (-65,0x38000000300000003)
  | ⟨true,false,false⟩ => (0,0x10000000700000007)
  | ⟨true,false,true⟩ => (-64,0x70000000700000001)
  | ⟨true,true,false⟩ => (-2,0x40000000700000007)
  | ⟨true,true,true⟩ => (-64,0x1c0000001c0000001)

set_option maxRecDepth 20000 in
private theorem view7x35 (g : Orientation) : cache7x35 g=views (shape 7 35) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x35x0 : RowFact 7 35 ⟨false,false,false⟩ :=
  checked_row (mask:=0x3c00000042000000420000008200000084000000840000007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x35 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x35x1 : RowFact 7 35 ⟨false,false,true⟩ :=
  checked_row (mask:=0x3800000044000000440000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x35 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x35x2 : RowFact 7 35 ⟨false,true,false⟩ :=
  checked_row (mask:=0xf00000010800000108000002080000010800000108000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x35 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x35x3 : RowFact 7 35 ⟨false,true,true⟩ :=
  checked_row (mask:=0x700000008800000088000001080000010800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x35 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x35x4 : RowFact 7 35 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3c000000420000004200000082000000820000008c0000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x35 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x35x5 : RowFact 7 35 ⟨true,false,true⟩ :=
  checked_row (mask:=0x300000004c000000420000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x35 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x35x6 : RowFact 7 35 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf000000108000001080000020800000208000001880000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x35 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x35x7 : RowFact 7 35 ⟨true,true,true⟩ :=
  checked_row (mask:=0x30000000c800000108000001080000020800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x35 (by decide +kernel) (by decide +kernel)

theorem checked7x35 (g : Orientation) : RowFact 7 35 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x35x0
  · exact part7x35x1
  · exact part7x35x2
  · exact part7x35x3
  · exact part7x35x4
  · exact part7x35x5
  · exact part7x35x6
  · exact part7x35x7

private def cache7x36 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x30000000700000003)
  | ⟨false,false,true⟩ => (-64,0x30000000700000003)
  | ⟨false,true,false⟩ => (-1,0x30000000380000003)
  | ⟨false,true,true⟩ => (-65,0x30000000380000003)
  | ⟨true,false,false⟩ => (0,0x20000000700000007)
  | ⟨true,false,true⟩ => (-63,0x38000000380000001)
  | ⟨true,true,false⟩ => (-2,0x20000000700000007)
  | ⟨true,true,true⟩ => (-65,0x38000000380000001)

set_option maxRecDepth 20000 in
private theorem view7x36 (g : Orientation) : cache7x36 g=views (shape 7 36) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x36x0 : RowFact 7 36 ⟨false,false,false⟩ :=
  checked_row (mask:=0x3800000044000000820000008200000082000000440000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x36 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x36x1 : RowFact 7 36 ⟨false,false,true⟩ :=
  checked_row (mask:=0x38000000440000008200000082000000820000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x36 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x36x2 : RowFact 7 36 ⟨false,true,false⟩ :=
  checked_row (mask:=0x7000000088000001080000020800000108000000880000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x36 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x36x3 : RowFact 7 36 ⟨false,true,true⟩ :=
  checked_row (mask:=0x70000000880000010800000208000001080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x36 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x36x4 : RowFact 7 36 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3c00000042000000820000008200000042000000240000001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x36 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x36x5 : RowFact 7 36 ⟨true,false,true⟩ :=
  checked_row (mask:=0x1800000024000000420000008200000082000000420000003c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x36 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x36x6 : RowFact 7 36 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf000000108000002080000020800000108000000900000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x36 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x36x7 : RowFact 7 36 ⟨true,true,true⟩ :=
  checked_row (mask:=0x600000009000000108000002080000020800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x36 (by decide +kernel) (by decide +kernel)

theorem checked7x36 (g : Orientation) : RowFact 7 36 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x36x0
  · exact part7x36x1
  · exact part7x36x2
  · exact part7x36x3
  · exact part7x36x4
  · exact part7x36x5
  · exact part7x36x6
  · exact part7x36x7

end HalfIndexRows
