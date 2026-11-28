import certificates.«pp-incidence-rows-core»

/-! All placements for free 8-cell tile indices 170, 171, 172, 174. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache8x170 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0xc000000070000000300000001)
  | ⟨false,false,true⟩ => (-94,0x40000000c0000001c0000003)
  | ⟨false,true,false⟩ => (0,0x60000001c000000180000001)
  | ⟨false,true,true⟩ => (-99,0x80000000c0000000e00000003)
  | ⟨true,false,false⟩ => (0,0x80000000c0000000600000007)
  | ⟨true,false,true⟩ => (-93,0xe0000000c000000180000001)
  | ⟨true,true,false⟩ => (-2,0x800000018000000300000007)
  | ⟨true,true,true⟩ => (-99,0xe000000060000000300000001)

set_option maxRecDepth 20000 in
private theorem view8x170 (g : Orientation) : cache8x170 g=views (shape 8 170) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x170x0 : RowFact 8 170 ⟨false,false,false⟩ :=
  checked_row (mask:=0xc00000013000000108000001040000008200000041000000210000001900000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x170 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x170x1 : RowFact 8 170 ⟨false,false,true⟩ :=
  checked_row (mask:=0x38000000c600000101000001010000010100000082000000440000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x170 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x170x2 : RowFact 8 170 ⟨false,true,false⟩ :=
  checked_row (mask:=0xc000000130000002080000040800000808000004080000020800000130000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x170 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x170x3 : RowFact 8 170 ⟨false,true,true⟩ :=
  checked_row (mask:=0x700000008c000000430000002080000010800000088000000480000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x170 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x170x4 : RowFact 8 170 ⟨true,false,false⟩ :=
  checked_row (mask:=0xf00000010c00000082000000420000002100000011000000090000000500000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x170 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x170x5 : RowFact 8 170 ⟨true,false,true⟩ :=
  checked_row (mask:=0x18000000260000004100000081000001010000008100000042000000220000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x170 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x170x6 : RowFact 8 170 ⟨true,true,false⟩ :=
  checked_row (mask:=0x3c00000043000000408000008080000080800000410000002200000014000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x170 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x170x7 : RowFact 8 170 ⟨true,true,true⟩ :=
  checked_row (mask:=0x6000000098000000840000004200000041000000208000001080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x170 (by decide +kernel) (by decide +kernel)

theorem checked8x170 (g : Orientation) : RowFact 8 170 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x170x0
  · exact part8x170x1
  · exact part8x170x2
  · exact part8x170x3
  · exact part8x170x4
  · exact part8x170x5
  · exact part8x170x6
  · exact part8x170x7

private def cache8x171 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x80000000f0000000300000001)
  | ⟨false,false,true⟩ => (-93,0x2000000060000001e0000001)
  | ⟨false,true,false⟩ => (0,0x20000001e000000180000001)
  | ⟨false,true,true⟩ => (-99,0x80000000c0000000f00000001)
  | ⟨true,false,false⟩ => (0,0xc000000040000000600000007)
  | ⟨true,false,true⟩ => (-94,0x1c00000018000000100000003)
  | ⟨true,true,false⟩ => (-2,0x1800000010000000300000007)
  | ⟨true,true,true⟩ => (-99,0xe000000060000000200000003)

set_option maxRecDepth 20000 in
private theorem view8x171 (g : Orientation) : cache8x171 g=views (shape 8 171) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x171x0 : RowFact 8 171 ⟨false,false,false⟩ :=
  checked_row (mask:=0x8000000170000001080000010600000101000000c1000000210000001d00000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x171 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x171x1 : RowFact 8 171 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000ee00000101000001010000010100000101000000c60000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x171 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x171x2 : RowFact 8 171 ⟨false,true,false⟩ :=
  checked_row (mask:=0x800000017000000608000008080000080800000808000006080000017000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x171 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x171x3 : RowFact 8 171 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000b8000000870000008080000060800000108000000c80000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x171 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x171x4 : RowFact 8 171 ⟨true,false,false⟩ :=
  checked_row (mask:=0xe00000011c00000102000000820000004200000041000000310000000900000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x171 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x171x5 : RowFact 8 171 ⟨true,false,true⟩ :=
  checked_row (mask:=0x300000004e00000041000000810000010100000102000000c2000000220000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x171 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x171x6 : RowFact 8 171 ⟨true,true,false⟩ :=
  checked_row (mask:=0x38000000470000004080000040800000808000008100000062000000120000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x171 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x171x7 : RowFact 8 171 ⟨true,true,true⟩ :=
  checked_row (mask:=0x600000009c000000820000004200000041000000408000003080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x171 (by decide +kernel) (by decide +kernel)

theorem checked8x171 (g : Orientation) : RowFact 8 171 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x171x0
  · exact part8x171x1
  · exact part8x171x2
  · exact part8x171x3
  · exact part8x171x4
  · exact part8x171x5
  · exact part8x171x6
  · exact part8x171x7

private def cache8x172 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x5000000070000000d)
  | ⟨false,false,true⟩ => (-64,0xd0000000700000005)
  | ⟨false,true,false⟩ => (-3,0xa0000000e0000000b)
  | ⟨false,true,true⟩ => (-66,0x58000000700000005)
  | ⟨true,false,false⟩ => (0,0x1000000070000000200000007)
  | ⟨true,false,true⟩ => (-96,0x7000000020000000700000001)
  | ⟨true,true,false⟩ => (-2,0x4000000070000000200000007)
  | ⟨true,true,true⟩ => (-96,0x1c000000080000001c0000001)

set_option maxRecDepth 20000 in
private theorem view8x172 (g : Orientation) : cache8x172 g=views (shape 8 172) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x172x0 : RowFact 8 172 ⟨false,false,false⟩ :=
  checked_row (mask:=0x5e000000a10000008100000101000001020000010a000000f400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x172 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x172x1 : RowFact 8 172 ⟨false,false,true⟩ :=
  checked_row (mask:=0x54000000aa00000082000001010000010100000101000000fe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x172 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x172x2 : RowFact 8 172 ⟨false,true,false⟩ :=
  checked_row (mask:=0x3d00000042800000408000008080000040800000428000003d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x172 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x172x3 : RowFact 8 172 ⟨false,true,true⟩ :=
  checked_row (mask:=0x150000002a800000208000004080000040800000828000007d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x172 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x172x4 : RowFact 8 172 ⟨true,false,false⟩ :=
  checked_row (mask:=0x7c00000082000000820000010200000082000001020000012c000000d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x172 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x172x5 : RowFact 8 172 ⟨true,false,true⟩ :=
  checked_row (mask:=0x50000000ac0000008200000102000001020000008200000102000000fc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x172 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x172x6 : RowFact 8 172 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1f0000002080000020800000408000002080000040800000328000000d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x172 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x172x7 : RowFact 8 172 ⟨true,true,true⟩ :=
  checked_row (mask:=0x50000001a80000020800000208000004080000020800000408000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x172 (by decide +kernel) (by decide +kernel)

theorem checked8x172 (g : Orientation) : RowFact 8 172 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x172x0
  · exact part8x172x1
  · exact part8x172x2
  · exact part8x172x3
  · exact part8x172x4
  · exact part8x172x5
  · exact part8x172x6
  · exact part8x172x7

private def cache8x174 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x10000000f0000000d)
  | ⟨false,false,true⟩ => (-64,0xd0000000f00000001)
  | ⟨false,true,false⟩ => (-3,0x80000000f0000000b)
  | ⟨false,true,true⟩ => (-64,0x160000001e0000001)
  | ⟨true,false,false⟩ => (0,0x3000000030000000200000007)
  | ⟨true,false,true⟩ => (-96,0x7000000020000000300000003)
  | ⟨true,true,false⟩ => (-2,0x6000000060000000200000007)
  | ⟨true,true,true⟩ => (-97,0x3800000010000000300000003)

set_option maxRecDepth 20000 in
private theorem view8x174 (g : Orientation) : cache8x174 g=views (shape 8 174) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x174x0 : RowFact 8 174 ⟨false,false,false⟩ :=
  checked_row (mask:=0x16000000e90000010100000101000001010000012e000000d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x174 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x174x1 : RowFact 8 174 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000ee00000101000001010000010100000101000000fe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x174 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x174x2 : RowFact 8 174 ⟨false,true,false⟩ :=
  checked_row (mask:=0xd00000072800000808000008080000080800000728000000d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x174 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x174x3 : RowFact 8 174 ⟨false,true,true⟩ :=
  checked_row (mask:=0x10000000e800000708000008080000080800000828000007d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x174 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x174x4 : RowFact 8 174 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1c000000e20000010200000102000001040000010400000104000000f8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x174 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x174x5 : RowFact 8 174 ⟨true,false,true⟩ :=
  checked_row (mask:=0x18000000e40000010400000104000001020000010200000102000000fc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x174 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x174x6 : RowFact 8 174 ⟨true,true,false⟩ :=
  checked_row (mask:=0x70000003880000040800000408000002080000020800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x174 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x174x7 : RowFact 8 174 ⟨true,true,true⟩ :=
  checked_row (mask:=0x30000001c80000020800000208000002080000040800000408000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x174 (by decide +kernel) (by decide +kernel)

theorem checked8x174 (g : Orientation) : RowFact 8 174 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x174x0
  · exact part8x174x1
  · exact part8x174x2
  · exact part8x174x3
  · exact part8x174x4
  · exact part8x174x5
  · exact part8x174x6
  · exact part8x174x7

end HalfIndexRows
