import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 37, 38, 39, 40. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x37 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x50000000700000003)
  | ⟨false,false,true⟩ => (-64,0x30000000700000005)
  | ⟨false,true,false⟩ => (-1,0x28000000380000003)
  | ⟨false,true,true⟩ => (-66,0x60000000700000005)
  | ⟨true,false,false⟩ => (0,0x60000000300000007)
  | ⟨true,false,true⟩ => (-63,0x38000000180000003)
  | ⟨true,true,false⟩ => (-2,0x30000000600000007)
  | ⟨true,true,true⟩ => (-66,0x70000000600000003)

set_option maxRecDepth 20000 in
private theorem view7x37 (g : Orientation) : cache7x37 g=views (shape 7 37) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x37x0 : RowFact 7 37 ⟨false,false,false⟩ :=
  checked_row (mask:=0x7800000084000000820000008200000082000000420000003c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x37 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x37x1 : RowFact 7 37 ⟨false,false,true⟩ :=
  checked_row (mask:=0x54000000aa0000008200000082000000820000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x37 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x37x2 : RowFact 7 37 ⟨false,true,false⟩ :=
  checked_row (mask:=0xf00000010800000208000002080000020800000108000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x37 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x37x3 : RowFact 7 37 ⟨false,true,true⟩ :=
  checked_row (mask:=0x150000002a80000020800000208000001080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x37 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x37x4 : RowFact 7 37 ⟨true,false,false⟩ :=
  checked_row (mask:=0x7c00000082000000820000008200000042000000220000001c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x37 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x37x5 : RowFact 7 37 ⟨true,false,true⟩ :=
  checked_row (mask:=0x3c00000042000000820000008200000082000000420000003c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x37 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x37x6 : RowFact 7 37 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1f00000020800000208000002080000020800000110000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x37 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x37x7 : RowFact 7 37 ⟨true,true,true⟩ :=
  checked_row (mask:=0x1e00000021000000208000002080000020800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x37 (by decide +kernel) (by decide +kernel)

theorem checked7x37 (g : Orientation) : RowFact 7 37 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x37x0
  · exact part7x37x1
  · exact part7x37x2
  · exact part7x37x3
  · exact part7x37x4
  · exact part7x37x5
  · exact part7x37x6
  · exact part7x37x7

private def cache7x38 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x10000000f00000003)
  | ⟨false,false,true⟩ => (-64,0x30000000f00000001)
  | ⟨false,true,false⟩ => (-1,0x200000003c0000003)
  | ⟨false,true,true⟩ => (-64,0x180000001e0000001)
  | ⟨true,false,false⟩ => (0,0x2000000020000000300000007)
  | ⟨true,false,true⟩ => (-95,0x3800000018000000100000001)
  | ⟨true,true,false⟩ => (-2,0x2000000020000000600000007)
  | ⟨true,true,true⟩ => (-97,0x3800000030000000100000001)

set_option maxRecDepth 20000 in
private theorem view7x38 (g : Orientation) : cache7x38 g=views (shape 7 38) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x38x0 : RowFact 7 38 ⟨false,false,false⟩ :=
  checked_row (mask:=0x18000000e6000001010000010100000101000000ce0000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x38 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x38x1 : RowFact 7 38 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000ee000001010000010100000101000000c600000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x38 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x38x2 : RowFact 7 38 ⟨false,true,false⟩ :=
  checked_row (mask:=0x30000001c8000006080000080800000608000001c80000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x38 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x38x3 : RowFact 7 38 ⟨false,true,true⟩ :=
  checked_row (mask:=0x10000000e80000070800000808000006080000018800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x38 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x38x4 : RowFact 7 38 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1c000000e2000001020000010200000084000000840000006400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x38 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x38x5 : RowFact 7 38 ⟨true,false,true⟩ :=
  checked_row (mask:=0x80000007400000084000000840000010200000102000000c20000003c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x38 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x38x6 : RowFact 7 38 ⟨true,true,false⟩ :=
  checked_row (mask:=0x7000000388000004080000020800000208000002100000019000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x38 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x38x7 : RowFact 7 38 ⟨true,true,true⟩ :=
  checked_row (mask:=0x20000001d00000021000000208000002080000040800000308000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x38 (by decide +kernel) (by decide +kernel)

theorem checked7x38 (g : Orientation) : RowFact 7 38 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x38x0
  · exact part7x38x1
  · exact part7x38x2
  · exact part7x38x3
  · exact part7x38x4
  · exact part7x38x5
  · exact part7x38x6
  · exact part7x38x7

private def cache7x39 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x2000000030000000100000007)
  | ⟨false,false,true⟩ => (-95,0x3800000008000000180000001)
  | ⟨false,true,false⟩ => (-2,0x2000000060000000400000007)
  | ⟨false,true,true⟩ => (-97,0x3800000020000000300000001)
  | ⟨true,false,false⟩ => (0,0x10000000d00000007)
  | ⟨true,false,true⟩ => (-64,0x70000000d00000001)
  | ⟨true,true,false⟩ => (-2,0x40000000580000007)
  | ⟨true,true,true⟩ => (-64,0x1c000000160000001)

set_option maxRecDepth 20000 in
private theorem view7x39 (g : Orientation) : cache7x39 g=views (shape 7 39) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x39x0 : RowFact 7 39 ⟨false,false,false⟩ :=
  checked_row (mask:=0x380000004400000042000000420000008200000084000000840000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x39 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x39x1 : RowFact 7 39 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000280000004400000044000000440000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x39 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x39x2 : RowFact 7 39 ⟨false,true,false⟩ :=
  checked_row (mask:=0xe000000110000001080000018800000208000001880000010800000110000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x39 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x39x3 : RowFact 7 39 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a0000000900000008800000108000001080000018800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x39 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x39x4 : RowFact 7 39 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3800000044000000420000004100000081000000810000008e0000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x39 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x39x5 : RowFact 7 39 ⟨true,false,true⟩ :=
  checked_row (mask:=0x200000005c00000042000000410000008100000081000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x39 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x39x6 : RowFact 7 39 ⟨true,true,false⟩ :=
  checked_row (mask:=0xe00000011000000208000002080000020800000408000003880000007000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x39 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x39x7 : RowFact 7 39 ⟨true,true,true⟩ :=
  checked_row (mask:=0x20000001d00000024800000208000003080000040800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x39 (by decide +kernel) (by decide +kernel)

theorem checked7x39 (g : Orientation) : RowFact 7 39 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x39x0
  · exact part7x39x1
  · exact part7x39x2
  · exact part7x39x3
  · exact part7x39x4
  · exact part7x39x5
  · exact part7x39x6
  · exact part7x39x7

private def cache7x40 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x2000000070000000100000003)
  | ⟨false,false,true⟩ => (-95,0x1800000008000000380000001)
  | ⟨false,true,false⟩ => (-1,0x1000000038000000200000003)
  | ⟨false,true,true⟩ => (-97,0x3000000020000000380000001)
  | ⟨true,false,false⟩ => (0,0x40000000d00000007)
  | ⟨true,false,true⟩ => (-62,0x1c000000340000001)
  | ⟨true,true,false⟩ => (-2,0x10000000580000007)
  | ⟨true,true,true⟩ => (-66,0x70000000580000001)

set_option maxRecDepth 20000 in
private theorem view7x40 (g : Orientation) : cache7x40 g=views (shape 7 40) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x40x0 : RowFact 7 40 ⟨false,false,false⟩ :=
  checked_row (mask:=0x300000004800000084000000840000008200000042000000420000002400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x40 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x40x1 : RowFact 7 40 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000820000008200000082000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x40 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x40x2 : RowFact 7 40 ⟨false,true,false⟩ :=
  checked_row (mask:=0x600000009000000108000001080000020800000108000001080000009000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x40 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x40x3 : RowFact 7 40 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a000000110000002080000018800000108000000c80000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x40 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x40x4 : RowFact 7 40 ⟨true,false,false⟩ :=
  checked_row (mask:=0x380000004400000082000000810000004100000041000000320000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x40 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x40x5 : RowFact 7 40 ⟨true,false,true⟩ :=
  checked_row (mask:=0x80000003400000042000000810000008100000041000000420000003c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x40 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x40x6 : RowFact 7 40 ⟨true,true,false⟩ :=
  checked_row (mask:=0xe0000001100000020800000408000002080000020800000130000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x40 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x40x7 : RowFact 7 40 ⟨true,true,true⟩ :=
  checked_row (mask:=0x80000001600000021000000408000002080000020800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x40 (by decide +kernel) (by decide +kernel)

theorem checked7x40 (g : Orientation) : RowFact 7 40 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x40x0
  · exact part7x40x1
  · exact part7x40x2
  · exact part7x40x3
  · exact part7x40x4
  · exact part7x40x5
  · exact part7x40x6
  · exact part7x40x7

end HalfIndexRows
