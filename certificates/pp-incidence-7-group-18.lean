import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 69, 70, 71, 72. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x69 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x3000000060000000300000001)
  | ⟨false,false,true⟩ => (-96,0x1000000030000000600000003)
  | ⟨false,true,false⟩ => (0,0x180000000c000000180000001)
  | ⟨false,true,true⟩ => (-97,0x2000000030000000180000003)
  | ⟨true,false,false⟩ => (0,0x40000000e0000000b)
  | ⟨true,false,true⟩ => (-62,0x2c000000380000001)
  | ⟨true,true,false⟩ => (-3,0x2000000070000000d)
  | ⟨true,true,true⟩ => (-66,0x68000000380000001)

set_option maxRecDepth 20000 in
private theorem view7x69 (g : Orientation) : cache7x69 g=views (shape 7 69) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x69x0 : RowFact 7 69 ⟨false,false,false⟩ :=
  checked_row (mask:=0x300000004800000084000000820000004400000082000000420000002400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x69 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x69x1 : RowFact 7 69 ⟨false,false,true⟩ :=
  checked_row (mask:=0x380000004400000082000000440000008200000082000000440000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x69 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x69x2 : RowFact 7 69 ⟨false,true,false⟩ :=
  checked_row (mask:=0x300000004800000088000001080000020800000108000000880000004800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x69 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x69x3 : RowFact 7 69 ⟨false,true,true⟩ :=
  checked_row (mask:=0x700000008800000110000002080000010800000088000000480000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x69 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x69x4 : RowFact 7 69 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3e00000041000000810000004100000021000000110000000a0000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x69 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x69x5 : RowFact 7 69 ⟨true,false,true⟩ :=
  checked_row (mask:=0xc0000001200000021000000410000008100000041000000250000001a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x69 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x69x6 : RowFact 7 69 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1f00000020800000410000004080000020800000110000000a00000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x69 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x69x7 : RowFact 7 69 ⟨true,true,true⟩ :=
  checked_row (mask:=0xc0000001200000021000000408000004100000020800000148000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x69 (by decide +kernel) (by decide +kernel)

theorem checked7x69 (g : Orientation) : RowFact 7 69 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x69x0
  · exact part7x69x1
  · exact part7x69x2
  · exact part7x69x3
  · exact part7x69x4
  · exact part7x69x5
  · exact part7x69x6
  · exact part7x69x7

private def cache7x70 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x2000000020000000700000003)
  | ⟨false,false,true⟩ => (-95,0x1800000038000000100000001)
  | ⟨false,true,false⟩ => (-1,0x1000000010000000380000003)
  | ⟨false,true,true⟩ => (-97,0x3000000038000000100000001)
  | ⟨true,false,false⟩ => (0,0x20000000f00000003)
  | ⟨true,false,true⟩ => (-63,0x18000000780000001)
  | ⟨true,true,false⟩ => (-1,0x100000003c0000003)
  | ⟨true,true,true⟩ => (-65,0x300000003c0000001)

set_option maxRecDepth 20000 in
private theorem view7x70 (g : Orientation) : cache7x70 g=views (shape 7 70) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x70x0 : RowFact 7 70 ⟨false,false,false⟩ :=
  checked_row (mask:=0x300000004800000044000000840000008200000042000000440000002400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x70 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x70x1 : RowFact 7 70 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000028000000440000004400000082000000820000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x70 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x70x2 : RowFact 7 70 ⟨false,true,false⟩ :=
  checked_row (mask:=0x600000009000000110000001080000020800000108000001100000009000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x70 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x70x3 : RowFact 7 70 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a0000000a0000001100000011000000208000001080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x70 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x70x4 : RowFact 7 70 ⟨true,false,false⟩ :=
  checked_row (mask:=0x300000004c00000042000000820000008100000041000000260000001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x70 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x70x5 : RowFact 7 70 ⟨true,false,true⟩ :=
  checked_row (mask:=0x100000002c000000420000004200000081000000810000004600000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x70 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x70x6 : RowFact 7 70 ⟨true,true,false⟩ :=
  checked_row (mask:=0x600000019000000210000002080000040800000208000001900000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x70 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x70x7 : RowFact 7 70 ⟨true,true,true⟩ :=
  checked_row (mask:=0x40000001a0000002100000021000000408000002080000018800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x70 (by decide +kernel) (by decide +kernel)

theorem checked7x70 (g : Orientation) : RowFact 7 70 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x70x0
  · exact part7x70x1
  · exact part7x70x2
  · exact part7x70x3
  · exact part7x70x4
  · exact part7x70x5
  · exact part7x70x6
  · exact part7x70x7

private def cache7x71 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x2000000060000000300000003)
  | ⟨false,false,true⟩ => (-95,0x1800000018000000300000001)
  | ⟨false,true,false⟩ => (-1,0x1000000018000000300000003)
  | ⟨false,true,true⟩ => (-97,0x3000000030000000180000001)
  | ⟨true,false,false⟩ => (0,0x40000000f00000003)
  | ⟨true,false,true⟩ => (-62,0xc0000003c0000001)
  | ⟨true,true,false⟩ => (-1,0x80000003c0000003)
  | ⟨true,true,true⟩ => (-66,0x60000000780000001)

set_option maxRecDepth 20000 in
private theorem view7x71 (g : Orientation) : cache7x71 g=views (shape 7 71) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x71x0 : RowFact 7 71 ⟨false,false,false⟩ :=
  checked_row (mask:=0x300000004800000088000000840000004400000042000000220000002400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x71 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x71x1 : RowFact 7 71 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000440000008200000082000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x71 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x71x2 : RowFact 7 71 ⟨false,true,false⟩ :=
  checked_row (mask:=0x600000009000000110000001080000020800000108000001100000009000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x71 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x71x3 : RowFact 7 71 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a000000120000002100000011000000108000000880000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x71 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x71x4 : RowFact 7 71 ⟨true,false,false⟩ :=
  checked_row (mask:=0x300000004c00000082000000820000004100000041000000320000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x71 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x71x5 : RowFact 7 71 ⟨true,false,true⟩ :=
  checked_row (mask:=0x800000034000000420000008200000081000000410000004600000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x71 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x71x6 : RowFact 7 71 ⟨true,true,false⟩ :=
  checked_row (mask:=0x60000001900000021000000408000002080000020800000130000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x71 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x71x7 : RowFact 7 71 ⟨true,true,true⟩ :=
  checked_row (mask:=0x8000000160000002100000041000000208000002080000018800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x71 (by decide +kernel) (by decide +kernel)

theorem checked7x71 (g : Orientation) : RowFact 7 71 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x71x0
  · exact part7x71x1
  · exact part7x71x2
  · exact part7x71x3
  · exact part7x71x4
  · exact part7x71x5
  · exact part7x71x6
  · exact part7x71x7

private def cache7x72 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x6000000020000000300000003)
  | ⟨false,false,true⟩ => (-95,0x1800000018000000100000003)
  | ⟨false,true,false⟩ => (-1,0x1800000010000000300000003)
  | ⟨false,true,true⟩ => (-98,0x6000000060000000200000003)
  | ⟨true,false,false⟩ => (0,0x80000000f00000003)
  | ⟨true,false,true⟩ => (-61,0x60000001e0000001)
  | ⟨true,true,false⟩ => (-1,0x40000003c0000003)
  | ⟨true,true,true⟩ => (-67,0xc0000000f00000001)

set_option maxRecDepth 20000 in
private theorem view7x72 (g : Orientation) : cache7x72 g=views (shape 7 72) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x72x0 : RowFact 7 72 ⟨false,false,false⟩ :=
  checked_row (mask:=0x70000000880000008800000044000000440000004400000022000000220000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x72 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x72x1 : RowFact 7 72 ⟨false,false,true⟩ :=
  checked_row (mask:=0x380000004400000044000000820000008200000044000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x72 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x72x2 : RowFact 7 72 ⟨false,true,false⟩ :=
  checked_row (mask:=0xe000000110000001100000010800000208000001080000011000000110000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x72 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x72x3 : RowFact 7 72 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1c00000022000000120000001100000011000000088000000880000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x72 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x72x4 : RowFact 7 72 ⟨true,false,false⟩ :=
  checked_row (mask:=0x700000008c00000082000000420000004100000041000000390000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x72 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x72x5 : RowFact 7 72 ⟨true,false,true⟩ :=
  checked_row (mask:=0xc00000072000000820000008100000041000000410000004600000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x72 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x72x6 : RowFact 7 72 ⟨true,true,false⟩ :=
  checked_row (mask:=0xe00000031000000410000004080000020800000208000002700000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x72 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x72x7 : RowFact 7 72 ⟨true,true,true⟩ :=
  checked_row (mask:=0x300000004e0000004100000021000000208000002080000018800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x72 (by decide +kernel) (by decide +kernel)

theorem checked7x72 (g : Orientation) : RowFact 7 72 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x72x0
  · exact part7x72x1
  · exact part7x72x2
  · exact part7x72x3
  · exact part7x72x4
  · exact part7x72x5
  · exact part7x72x6
  · exact part7x72x7

end HalfIndexRows
