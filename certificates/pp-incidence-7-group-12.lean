import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 45, 46, 47, 48. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x45 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x2000000030000000700000001)
  | ⟨false,false,true⟩ => (-95,0x800000038000000180000001)
  | ⟨false,true,false⟩ => (0,0x8000000180000001c0000001)
  | ⟨false,true,true⟩ => (-97,0x2000000038000000300000001)
  | ⟨true,false,false⟩ => (0,0x20000000e00000007)
  | ⟨true,false,true⟩ => (-63,0x38000000700000001)
  | ⟨true,true,false⟩ => (-2,0x20000000380000007)
  | ⟨true,true,true⟩ => (-65,0x380000001c0000001)

set_option maxRecDepth 20000 in
private theorem view7x45 (g : Orientation) : cache7x45 g=views (shape 7 45) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x45x0 : RowFact 7 45 ⟨false,false,false⟩ :=
  checked_row (mask:=0x200000005800000044000000820000008200000082000000440000003400000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x45 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x45x1 : RowFact 7 45 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000440000008200000082000000820000006c00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x45 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x45x2 : RowFact 7 45 ⟨false,true,false⟩ :=
  checked_row (mask:=0x20000000d00000010800000108000002080000010800000108000000d000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x45 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x45x3 : RowFact 7 45 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a000000090000001080000010800000208000001880000006800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x45 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x45x4 : RowFact 7 45 ⟨true,false,false⟩ :=
  checked_row (mask:=0x380000004400000042000000810000004100000041000000360000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x45 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x45x5 : RowFact 7 45 ⟨true,false,true⟩ :=
  checked_row (mask:=0x100000002c00000022000000410000004100000081000000620000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x45 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x45x6 : RowFact 7 45 ⟨true,true,false⟩ :=
  checked_row (mask:=0xe00000011000000208000002080000040800000310000000d00000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x45 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x45x7 : RowFact 7 45 ⟨true,true,true⟩ :=
  checked_row (mask:=0x40000001a0000002100000021000000408000002080000018800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x45 (by decide +kernel) (by decide +kernel)

theorem checked7x45 (g : Orientation) : RowFact 7 45 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x45x0
  · exact part7x45x1
  · exact part7x45x2
  · exact part7x45x3
  · exact part7x45x4
  · exact part7x45x5
  · exact part7x45x6
  · exact part7x45x7

private def cache7x46 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x2000000070000000300000001)
  | ⟨false,false,true⟩ => (-95,0x800000018000000380000001)
  | ⟨false,true,false⟩ => (0,0x80000001c000000180000001)
  | ⟨false,true,true⟩ => (-97,0x2000000030000000380000001)
  | ⟨true,false,false⟩ => (0,0x40000000e00000007)
  | ⟨true,false,true⟩ => (-62,0x1c000000380000001)
  | ⟨true,true,false⟩ => (-2,0x10000000380000007)
  | ⟨true,true,true⟩ => (-66,0x70000000380000001)

set_option maxRecDepth 20000 in
private theorem view7x46 (g : Orientation) : cache7x46 g=views (shape 7 46) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x46x0 : RowFact 7 46 ⟨false,false,false⟩ :=
  checked_row (mask:=0x200000005000000088000000840000008200000042000000220000001400000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x46 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x46x1 : RowFact 7 46 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000820000008200000082000000440000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x46 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x46x2 : RowFact 7 46 ⟨false,true,false⟩ :=
  checked_row (mask:=0x200000005000000088000001080000020800000108000000880000005000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x46 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x46x3 : RowFact 7 46 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a000000110000002080000010800000088000000480000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x46 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x46x4 : RowFact 7 46 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3800000044000000820000004100000021000000110000000a0000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x46 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x46x5 : RowFact 7 46 ⟨true,false,true⟩ :=
  checked_row (mask:=0x80000001400000022000000410000008100000041000000220000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x46 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x46x6 : RowFact 7 46 ⟨true,true,false⟩ :=
  checked_row (mask:=0xe00000011000000208000004080000020800000110000000a00000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x46 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x46x7 : RowFact 7 46 ⟨true,true,true⟩ :=
  checked_row (mask:=0x8000000140000002200000041000000208000001080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x46 (by decide +kernel) (by decide +kernel)

theorem checked7x46 (g : Orientation) : RowFact 7 46 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x46x0
  · exact part7x46x1
  · exact part7x46x2
  · exact part7x46x3
  · exact part7x46x4
  · exact part7x46x5
  · exact part7x46x6
  · exact part7x46x7

private def cache7x47 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x6000000030000000300000001)
  | ⟨false,false,true⟩ => (-95,0x800000018000000180000003)
  | ⟨false,true,false⟩ => (0,0xc00000018000000180000001)
  | ⟨false,true,true⟩ => (-98,0x4000000060000000600000003)
  | ⟨true,false,false⟩ => (0,0x80000000e00000007)
  | ⟨true,false,true⟩ => (-61,0xe0000001c0000001)
  | ⟨true,true,false⟩ => (-2,0x8000000380000007)
  | ⟨true,true,true⟩ => (-67,0xe0000000700000001)

set_option maxRecDepth 20000 in
private theorem view7x47 (g : Orientation) : cache7x47 g=views (shape 7 47) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x47x0 : RowFact 7 47 ⟨false,false,false⟩ :=
  checked_row (mask:=0x60000000900000008800000084000000440000004200000022000000120000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x47 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x47x1 : RowFact 7 47 ⟨false,false,true⟩ :=
  checked_row (mask:=0x380000004400000082000000820000008200000044000000440000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x47 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x47x2 : RowFact 7 47 ⟨false,true,false⟩ :=
  checked_row (mask:=0x600000009000000108000001080000020800000108000001080000009000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x47 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x47x3 : RowFact 7 47 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1c00000022000000110000001080000008800000088000000480000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x47 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x47x4 : RowFact 7 47 ⟨true,false,false⟩ :=
  checked_row (mask:=0x7800000084000000420000004100000021000000110000000d0000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x47 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x47x5 : RowFact 7 47 ⟨true,false,true⟩ :=
  checked_row (mask:=0xc0000003200000041000000810000004100000041000000220000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x47 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x47x6 : RowFact 7 47 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1e00000021000000408000004080000020800000210000001600000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x47 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x47x7 : RowFact 7 47 ⟨true,true,true⟩ :=
  checked_row (mask:=0x300000004c0000004200000021000000208000001080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x47 (by decide +kernel) (by decide +kernel)

theorem checked7x47 (g : Orientation) : RowFact 7 47 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x47x0
  · exact part7x47x1
  · exact part7x47x2
  · exact part7x47x3
  · exact part7x47x4
  · exact part7x47x5
  · exact part7x47x6
  · exact part7x47x7

private def cache7x48 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x4000000070000000300000001)
  | ⟨false,false,true⟩ => (-94,0x40000000c0000001c0000001)
  | ⟨false,true,false⟩ => (0,0x40000001c000000180000001)
  | ⟨false,true,true⟩ => (-98,0x4000000060000000700000001)
  | ⟨true,false,false⟩ => (0,0xc0000000600000007)
  | ⟨true,false,true⟩ => (-62,0x1c000000180000003)
  | ⟨true,true,false⟩ => (-2,0x18000000300000007)
  | ⟨true,true,true⟩ => (-67,0xe0000000600000003)

set_option maxRecDepth 20000 in
private theorem view7x48 (g : Orientation) : cache7x48 g=views (shape 7 48) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x48x0 : RowFact 7 48 ⟨false,false,false⟩ :=
  checked_row (mask:=0x40000000b000000088000000840000008200000042000000220000001a00000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x48 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x48x1 : RowFact 7 48 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c00000082000000820000008200000082000000440000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x48 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x48x2 : RowFact 7 48 ⟨false,true,false⟩ :=
  checked_row (mask:=0x40000000b00000010800000208000002080000020800000108000000b000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x48 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x48x3 : RowFact 7 48 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000002c000000230000002080000010800000088000000480000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x48 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x48x4 : RowFact 7 48 ⟨true,false,false⟩ :=
  checked_row (mask:=0x700000008c00000082000000420000002100000011000000090000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x48 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x48x5 : RowFact 7 48 ⟨true,false,true⟩ :=
  checked_row (mask:=0x180000002600000041000000810000008100000042000000220000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x48 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x48x6 : RowFact 7 48 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1c0000002300000020800000408000004080000021000000120000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x48 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x48x7 : RowFact 7 48 ⟨true,true,true⟩ :=
  checked_row (mask:=0x300000004c0000004200000021000000208000001080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x48 (by decide +kernel) (by decide +kernel)

theorem checked7x48 (g : Orientation) : RowFact 7 48 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x48x0
  · exact part7x48x1
  · exact part7x48x2
  · exact part7x48x3
  · exact part7x48x4
  · exact part7x48x5
  · exact part7x48x6
  · exact part7x48x7

end HalfIndexRows
