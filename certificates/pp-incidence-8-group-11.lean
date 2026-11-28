import certificates.«pp-incidence-rows-core»

/-! All placements for free 8-cell tile indices 127, 131, 138, 141. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache8x127 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x70000000300000007)
  | ⟨false,false,true⟩ => (-64,0x70000000300000007)
  | ⟨false,true,false⟩ => (-2,0x70000000600000007)
  | ⟨false,true,true⟩ => (-66,0x70000000600000007)
  | ⟨true,false,false⟩ => (0,0x50000000700000007)
  | ⟨true,false,true⟩ => (-64,0x70000000700000005)
  | ⟨true,true,false⟩ => (-2,0x50000000700000007)
  | ⟨true,true,true⟩ => (-66,0x70000000700000005)

set_option maxRecDepth 20000 in
private theorem view8x127 (g : Orientation) : cache8x127 g=views (shape 8 127) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x127x0 : RowFact 8 127 ⟨false,false,false⟩ :=
  checked_row (mask:=0x7c00000082000000820000008200000082000000820000007c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x127 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x127x1 : RowFact 8 127 ⟨false,false,true⟩ :=
  checked_row (mask:=0x7c00000082000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x127 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x127x2 : RowFact 8 127 ⟨false,true,false⟩ :=
  checked_row (mask:=0x1f00000020800000108000002080000010800000208000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x127 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x127x3 : RowFact 8 127 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1f00000020800000108000002080000010800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x127 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x127x4 : RowFact 8 127 ⟨true,false,false⟩ :=
  checked_row (mask:=0x7c00000082000000820000008200000082000000820000007c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x127 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x127x5 : RowFact 8 127 ⟨true,false,true⟩ :=
  checked_row (mask:=0x7c00000082000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x127 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x127x6 : RowFact 8 127 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1f00000020800000208000002080000020800000208000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x127 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x127x7 : RowFact 8 127 ⟨true,true,true⟩ :=
  checked_row (mask:=0x1f00000020800000208000002080000020800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x127 (by decide +kernel) (by decide +kernel)

theorem checked8x127 (g : Orientation) : RowFact 8 127 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x127x0
  · exact part8x127x1
  · exact part8x127x2
  · exact part8x127x3
  · exact part8x127x4
  · exact part8x127x5
  · exact part8x127x6
  · exact part8x127x7

private def cache8x131 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x50000000f00000003)
  | ⟨false,false,true⟩ => (-64,0x30000000f00000005)
  | ⟨false,true,false⟩ => (-1,0x280000003c0000003)
  | ⟨false,true,true⟩ => (-66,0x60000000780000005)
  | ⟨true,false,false⟩ => (0,0x2000000060000000300000007)
  | ⟨true,false,true⟩ => (-95,0x3800000018000000300000001)
  | ⟨true,true,false⟩ => (-2,0x2000000030000000600000007)
  | ⟨true,true,true⟩ => (-97,0x3800000030000000180000001)

set_option maxRecDepth 20000 in
private theorem view8x131 (g : Orientation) : cache8x131 g=views (shape 8 131) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x131x0 : RowFact 8 131 ⟨false,false,false⟩ :=
  checked_row (mask:=0x7800000086000001010000010100000101000000c20000003c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x131 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x131x1 : RowFact 8 131 ⟨false,false,true⟩ :=
  checked_row (mask:=0x54000000aa000001010000010100000101000000c600000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x131 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x131x2 : RowFact 8 131 ⟨false,true,false⟩ :=
  checked_row (mask:=0xf00000030800000408000008080000040800000308000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x131 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x131x3 : RowFact 8 131 ⟨false,true,true⟩ :=
  checked_row (mask:=0x150000002a80000040800000808000006080000018800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x131 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x131x4 : RowFact 8 131 ⟨true,false,false⟩ :=
  checked_row (mask:=0x7c00000082000001020000010200000082000000820000006400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x131 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x131x5 : RowFact 8 131 ⟨true,false,true⟩ :=
  checked_row (mask:=0x280000005400000082000000820000010200000102000000c20000003c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x131 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x131x6 : RowFact 8 131 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1f000000208000004080000020800000408000002100000019000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x131 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x131x7 : RowFact 8 131 ⟨true,true,true⟩ :=
  checked_row (mask:=0xa0000001500000021000000408000002080000040800000308000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x131 (by decide +kernel) (by decide +kernel)

theorem checked8x131 (g : Orientation) : RowFact 8 131 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x131x0
  · exact part8x131x1
  · exact part8x131x2
  · exact part8x131x3
  · exact part8x131x4
  · exact part8x131x5
  · exact part8x131x6
  · exact part8x131x7

private def cache8x138 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x200000006000000030000000100000003)
  | ⟨false,false,true⟩ => (-127,0x180000000800000018000000300000001)
  | ⟨false,true,false⟩ => (-1,0x100000001800000030000000200000003)
  | ⟨false,true,true⟩ => (-129,0x300000002000000030000000180000001)
  | ⟨true,false,false⟩ => (0,0x80000001d00000007)
  | ⟨true,false,true⟩ => (-61,0xe0000003a0000001)
  | ⟨true,true,false⟩ => (-2,0x80000005c0000007)
  | ⟨true,true,true⟩ => (-67,0xe0000000b80000001)

set_option maxRecDepth 20000 in
private theorem view8x138 (g : Orientation) : cache8x138 g=views (shape 8 138) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x138x0 : RowFact 8 138 ⟨false,false,false⟩ :=
  checked_row (mask:=0x30000000480000008800000084000000840000004400000042000000420000002200000024000000180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x138 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x138x1 : RowFact 8 138 ⟨false,false,true⟩ :=
  checked_row (mask:=0x1000000028000000440000004400000082000000820000008200000044000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x138 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x138x2 : RowFact 8 138 ⟨false,true,false⟩ :=
  checked_row (mask:=0x60000000900000011000000088000001080000020800000108000000880000011000000090000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x138 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x138x3 : RowFact 8 138 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a0000001200000021000000110000000880000010800000088000000480000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x138 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x138x4 : RowFact 8 138 ⟨true,false,false⟩ :=
  checked_row (mask:=0x38000000460000008100000081000000408000004080000040800000390000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x138 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x138x5 : RowFact 8 138 ⟨true,false,true⟩ :=
  checked_row (mask:=0x40000002a0000005100000081000000808000004080000040800000430000003c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x138 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x138x6 : RowFact 8 138 ⟨true,true,false⟩ :=
  checked_row (mask:=0xe0000003100000041000000808000004080000020800000408000002700000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x138 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x138x7 : RowFact 8 138 ⟨true,true,true⟩ :=
  checked_row (mask:=0x100000002a0000004500000081000000408000002080000040800000308000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x138 (by decide +kernel) (by decide +kernel)

theorem checked8x138 (g : Orientation) : RowFact 8 138 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x138x0
  · exact part8x138x1
  · exact part8x138x2
  · exact part8x138x3
  · exact part8x138x4
  · exact part8x138x5
  · exact part8x138x6
  · exact part8x138x7

private def cache8x141 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x2000000070000000100000007)
  | ⟨false,false,true⟩ => (-95,0x3800000008000000380000001)
  | ⟨false,true,false⟩ => (-2,0x2000000070000000400000007)
  | ⟨false,true,true⟩ => (-97,0x3800000020000000380000001)
  | ⟨true,false,false⟩ => (0,0x50000000d00000007)
  | ⟨true,false,true⟩ => (-64,0x70000000d00000005)
  | ⟨true,true,false⟩ => (-2,0x50000000580000007)
  | ⟨true,true,true⟩ => (-66,0x70000000580000005)

set_option maxRecDepth 20000 in
private theorem view8x141 (g : Orientation) : cache8x141 g=views (shape 8 141) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x141x0 : RowFact 8 141 ⟨false,false,false⟩ :=
  checked_row (mask:=0x380000004400000082000000820000008200000082000000820000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x141 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x141x1 : RowFact 8 141 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000280000004400000082000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x141 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x141x2 : RowFact 8 141 ⟨false,true,false⟩ :=
  checked_row (mask:=0xe000000110000002080000010800000208000001080000020800000110000000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x141 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x141x3 : RowFact 8 141 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a0000001100000020800000108000002080000018800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x141 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x141x4 : RowFact 8 141 ⟨true,false,false⟩ :=
  checked_row (mask:=0x380000004400000082000000810000008100000081000000820000007c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x141 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x141x5 : RowFact 8 141 ⟨true,false,true⟩ :=
  checked_row (mask:=0x280000005400000082000000810000008100000081000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x141 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x141x6 : RowFact 8 141 ⟨true,true,false⟩ :=
  checked_row (mask:=0xe0000001100000020800000408000002080000040800000208000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x141 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x141x7 : RowFact 8 141 ⟨true,true,true⟩ :=
  checked_row (mask:=0xa0000001500000020800000408000002080000040800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x141 (by decide +kernel) (by decide +kernel)

theorem checked8x141 (g : Orientation) : RowFact 8 141 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x141x0
  · exact part8x141x1
  · exact part8x141x2
  · exact part8x141x3
  · exact part8x141x4
  · exact part8x141x5
  · exact part8x141x6
  · exact part8x141x7

end HalfIndexRows
