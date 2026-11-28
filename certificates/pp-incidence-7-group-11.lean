import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 41, 42, 43, 44. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x41 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x6000000030000000100000003)
  | ⟨false,false,true⟩ => (-95,0x1800000008000000180000003)
  | ⟨false,true,false⟩ => (-1,0x1800000030000000200000003)
  | ⟨false,true,true⟩ => (-98,0x6000000040000000600000003)
  | ⟨true,false,false⟩ => (0,0x80000000d00000007)
  | ⟨true,false,true⟩ => (-61,0xe0000001a0000001)
  | ⟨true,true,false⟩ => (-2,0x8000000580000007)
  | ⟨true,true,true⟩ => (-67,0xe0000000b00000001)

set_option maxRecDepth 20000 in
private theorem view7x41 (g : Orientation) : cache7x41 g=views (shape 7 41) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x41x0 : RowFact 7 41 ⟨false,false,false⟩ :=
  checked_row (mask:=0x70000000880000008400000084000000440000004200000042000000220000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x41 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x41x1 : RowFact 7 41 ⟨false,false,true⟩ :=
  checked_row (mask:=0x380000004400000082000000820000008200000044000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x41 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x41x2 : RowFact 7 41 ⟨false,true,false⟩ :=
  checked_row (mask:=0xe000000110000000880000010800000208000001080000008800000110000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x41 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x41x3 : RowFact 7 41 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1c00000022000000110000000880000010800000088000000480000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x41 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x41x4 : RowFact 7 41 ⟨true,false,false⟩ :=
  checked_row (mask:=0x780000008400000082000000410000004100000041000000390000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x41 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x41x5 : RowFact 7 41 ⟨true,false,true⟩ :=
  checked_row (mask:=0xc0000007200000081000000810000004100000041000000420000003c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x41 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x41x6 : RowFact 7 41 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1e00000021000000408000004080000020800000208000002700000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x41 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x41x7 : RowFact 7 41 ⟨true,true,true⟩ :=
  checked_row (mask:=0x300000004e00000041000000208000002080000020800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x41 (by decide +kernel) (by decide +kernel)

theorem checked7x41 (g : Orientation) : RowFact 7 41 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x41x0
  · exact part7x41x1
  · exact part7x41x2
  · exact part7x41x3
  · exact part7x41x4
  · exact part7x41x5
  · exact part7x41x6
  · exact part7x41x7

private def cache7x42 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x30000000500000007)
  | ⟨false,false,true⟩ => (-64,0x70000000500000003)
  | ⟨false,true,false⟩ => (-2,0x60000000500000007)
  | ⟨false,true,true⟩ => (-65,0x38000000280000003)
  | ⟨true,false,false⟩ => (0,0x30000000500000007)
  | ⟨true,false,true⟩ => (-64,0x70000000500000003)
  | ⟨true,true,false⟩ => (-2,0x60000000500000007)
  | ⟨true,true,true⟩ => (-65,0x38000000280000003)

set_option maxRecDepth 20000 in
private theorem view7x42 (g : Orientation) : cache7x42 g=views (shape 7 42) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x42x0 : RowFact 7 42 ⟨false,false,false⟩ :=
  checked_row (mask:=0x3c00000042000000820000008200000082000000840000007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x42 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x42x1 : RowFact 7 42 ⟨false,false,true⟩ :=
  checked_row (mask:=0x3800000044000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x42 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x42x2 : RowFact 7 42 ⟨false,true,false⟩ :=
  checked_row (mask:=0xf00000010800000208000002080000020800000108000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x42 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x42x3 : RowFact 7 42 ⟨false,true,true⟩ :=
  checked_row (mask:=0x700000008800000108000002080000020800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x42 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x42x4 : RowFact 7 42 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3c00000042000000820000008200000082000000840000007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x42 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x42x5 : RowFact 7 42 ⟨true,false,true⟩ :=
  checked_row (mask:=0x3800000044000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x42 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x42x6 : RowFact 7 42 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf00000010800000208000002080000020800000108000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x42 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x42x7 : RowFact 7 42 ⟨true,true,true⟩ :=
  checked_row (mask:=0x700000008800000108000002080000020800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x42 (by decide +kernel) (by decide +kernel)

theorem checked7x42 (g : Orientation) : RowFact 7 42 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x42x0
  · exact part7x42x1
  · exact part7x42x2
  · exact part7x42x3
  · exact part7x42x4
  · exact part7x42x5
  · exact part7x42x6
  · exact part7x42x7

private def cache7x43 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x70000000100000007)
  | ⟨false,false,true⟩ => (-64,0x70000000100000007)
  | ⟨false,true,false⟩ => (-2,0x70000000400000007)
  | ⟨false,true,true⟩ => (-66,0x70000000400000007)
  | ⟨true,false,false⟩ => (0,0x50000000500000007)
  | ⟨true,false,true⟩ => (-64,0x70000000500000005)
  | ⟨true,true,false⟩ => (-2,0x50000000500000007)
  | ⟨true,true,true⟩ => (-66,0x70000000500000005)

set_option maxRecDepth 20000 in
private theorem view7x43 (g : Orientation) : cache7x43 g=views (shape 7 43) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x43x0 : RowFact 7 43 ⟨false,false,false⟩ :=
  checked_row (mask:=0x7c00000082000000820000008200000082000000820000007c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x43 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x43x1 : RowFact 7 43 ⟨false,false,true⟩ :=
  checked_row (mask:=0x7c00000082000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x43 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x43x2 : RowFact 7 43 ⟨false,true,false⟩ :=
  checked_row (mask:=0x1f00000020800000188000002080000018800000208000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x43 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x43x3 : RowFact 7 43 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1f00000020800000188000002080000018800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x43 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x43x4 : RowFact 7 43 ⟨true,false,false⟩ :=
  checked_row (mask:=0x7c00000082000000820000008200000082000000820000007c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x43 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x43x5 : RowFact 7 43 ⟨true,false,true⟩ :=
  checked_row (mask:=0x7c00000082000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x43 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x43x6 : RowFact 7 43 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1f00000020800000208000002080000020800000208000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x43 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x43x7 : RowFact 7 43 ⟨true,true,true⟩ :=
  checked_row (mask:=0x1f00000020800000208000002080000020800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x43 (by decide +kernel) (by decide +kernel)

theorem checked7x43 (g : Orientation) : RowFact 7 43 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x43x0
  · exact part7x43x1
  · exact part7x43x2
  · exact part7x43x3
  · exact part7x43x4
  · exact part7x43x5
  · exact part7x43x6
  · exact part7x43x7

private def cache7x44 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x4000000070000000100000003)
  | ⟨false,false,true⟩ => (-94,0xc000000040000001c0000001)
  | ⟨false,true,false⟩ => (-1,0x800000038000000200000003)
  | ⟨false,true,true⟩ => (-98,0x6000000040000000700000001)
  | ⟨true,false,false⟩ => (0,0xc0000000500000007)
  | ⟨true,false,true⟩ => (-62,0x1c000000140000003)
  | ⟨true,true,false⟩ => (-2,0x18000000500000007)
  | ⟨true,true,true⟩ => (-67,0xe0000000a00000003)

set_option maxRecDepth 20000 in
private theorem view7x44 (g : Orientation) : cache7x44 g=views (shape 7 44) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x44x0 : RowFact 7 44 ⟨false,false,false⟩ :=
  checked_row (mask:=0x60000000980000008400000084000000820000004200000042000000320000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x44 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x44x1 : RowFact 7 44 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c00000082000000820000008200000082000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x44 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x44x2 : RowFact 7 44 ⟨false,true,false⟩ :=
  checked_row (mask:=0xc000000130000001080000020800000208000002080000010800000130000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x44 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x44x3 : RowFact 7 44 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000002c000000230000002080000010800000108000000c80000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x44 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x44x4 : RowFact 7 44 ⟨true,false,false⟩ :=
  checked_row (mask:=0x700000008c00000082000000820000004100000041000000310000000e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x44 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x44x5 : RowFact 7 44 ⟨true,false,true⟩ :=
  checked_row (mask:=0x1800000066000000a1000000810000008100000042000000420000003c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x44 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x44x6 : RowFact 7 44 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1c0000002300000020800000408000004080000030800000230000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x44 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x44x7 : RowFact 7 44 ⟨true,true,true⟩ :=
  checked_row (mask:=0x300000004c00000043000000208000002080000010800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x44 (by decide +kernel) (by decide +kernel)

theorem checked7x44 (g : Orientation) : RowFact 7 44 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x44x0
  · exact part7x44x1
  · exact part7x44x2
  · exact part7x44x3
  · exact part7x44x4
  · exact part7x44x5
  · exact part7x44x6
  · exact part7x44x7

end HalfIndexRows
