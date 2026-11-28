import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 93, 94, 95, 96. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x93 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x40000000f00000005)
  | ⟨false,false,true⟩ => (-62,0x140000003c0000001)
  | ⟨false,true,false⟩ => (-2,0x10000000780000005)
  | ⟨false,true,true⟩ => (-66,0x50000000780000001)
  | ⟨true,false,false⟩ => (0,0x2000000070000000200000003)
  | ⟨true,false,true⟩ => (-95,0x1800000010000000380000001)
  | ⟨true,true,false⟩ => (-1,0x1000000038000000100000003)
  | ⟨true,true,true⟩ => (-97,0x3000000010000000380000001)

set_option maxRecDepth 20000 in
private theorem view7x93 (g : Orientation) : cache7x93 g=views (shape 7 93) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x93x0 : RowFact 7 93 ⟨false,false,false⟩ :=
  checked_row (mask:=0x50000000ac0000010200000101000000810000006a0000001400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x93 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x93x1 : RowFact 7 93 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c000000820000010100000101000000aa00000054000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x93 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x93x2 : RowFact 7 93 ⟨false,true,false⟩ :=
  checked_row (mask:=0x140000002b0000004080000080800000408000002b00000014000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x93 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x93x3 : RowFact 7 93 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000002c0000004300000080800000408000002a800000150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x93 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x93x4 : RowFact 7 93 ⟨true,false,false⟩ :=
  checked_row (mask:=0x6000000098000001040000008400000102000000820000005400000028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x93 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x93x5 : RowFact 7 93 ⟨true,false,true⟩ :=
  checked_row (mask:=0x2000000058000000840000010200000082000001040000008400000078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x93 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x93x6 : RowFact 7 93 ⟨true,true,false⟩ :=
  checked_row (mask:=0xc0000001300000020800000208000004080000020800000150000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x93 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x93x7 : RowFact 7 93 ⟨true,true,true⟩ :=
  checked_row (mask:=0x80000001600000021000000408000002080000020800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x93 (by decide +kernel) (by decide +kernel)

theorem checked7x93 (g : Orientation) : RowFact 7 93 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x93x0
  · exact part7x93x1
  · exact part7x93x2
  · exact part7x93x3
  · exact part7x93x4
  · exact part7x93x5
  · exact part7x93x6
  · exact part7x93x7

private def cache7x94 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x4000000040000000f00000001)
  | ⟨false,false,true⟩ => (-94,0x40000003c000000100000001)
  | ⟨false,true,false⟩ => (0,0x4000000040000001e0000001)
  | ⟨false,true,true⟩ => (-98,0x4000000078000000100000001)
  | ⟨true,false,false⟩ => (0,0x20000000e0000000200000003)
  | ⟨true,false,true⟩ => (-95,0x1800000010000000700000001)
  | ⟨true,true,false⟩ => (-1,0x100000001c000000100000003)
  | ⟨true,true,true⟩ => (-97,0x30000000100000001c0000001)

set_option maxRecDepth 20000 in
private theorem view7x94 (g : Orientation) : cache7x94 g=views (shape 7 94) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x94x0 : RowFact 7 94 ⟨false,false,false⟩ :=
  checked_row (mask:=0x40000000b8000000840000010600000101000000c1000000420000003a00000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x94 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x94x1 : RowFact 7 94 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000280000006c00000082000000820000010100000101000000ee00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x94 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x94x2 : RowFact 7 94 ⟨false,true,false⟩ :=
  checked_row (mask:=0x40000003a00000043000000408000008080000040800000430000003a000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x94 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x94x3 : RowFact 7 94 ⟨false,true,true⟩ :=
  checked_row (mask:=0x10000000280000002c000000420000004300000080800000708000000e800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x94 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x94x4 : RowFact 7 94 ⟨true,false,false⟩ :=
  checked_row (mask:=0x600000009000000098000001040000008600000081000000810000007600000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x94 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x94x5 : RowFact 7 94 ⟨true,false,true⟩ :=
  checked_row (mask:=0x20000000580000004400000086000000810000008100000106000000e400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x94 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x94x6 : RowFact 7 94 ⟨true,true,false⟩ :=
  checked_row (mask:=0xc0000001200000033000000408000004080000081000000610000001d000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x94 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x94x7 : RowFact 7 94 ⟨true,true,true⟩ :=
  checked_row (mask:=0x80000003400000046000000410000008100000061000000208000001c800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x94 (by decide +kernel) (by decide +kernel)

theorem checked7x94 (g : Orientation) : RowFact 7 94 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x94x0
  · exact part7x94x1
  · exact part7x94x2
  · exact part7x94x3
  · exact part7x94x4
  · exact part7x94x5
  · exact part7x94x6
  · exact part7x94x7

private def cache7x95 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x40000000c0000000700000001)
  | ⟨false,false,true⟩ => (-94,0x40000001c000000300000001)
  | ⟨false,true,false⟩ => (0,0x4000000060000001c0000001)
  | ⟨false,true,true⟩ => (-98,0x4000000070000000180000001)
  | ⟨true,false,false⟩ => (0,0x40000000e0000000200000003)
  | ⟨true,false,true⟩ => (-94,0xc00000008000000380000001)
  | ⟨true,true,false⟩ => (-1,0x80000001c000000100000003)
  | ⟨true,true,true⟩ => (-98,0x6000000020000000380000001)

set_option maxRecDepth 20000 in
private theorem view7x95 (g : Orientation) : cache7x95 g=views (shape 7 95) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x95x0 : RowFact 7 95 ⟨false,false,false⟩ :=
  checked_row (mask:=0x40000000b000000108000001040000008200000041000000210000001a00000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x95 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x95x1 : RowFact 7 95 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000820000010100000101000000820000006c00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x95 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x95x2 : RowFact 7 95 ⟨false,true,false⟩ :=
  checked_row (mask:=0x40000001a00000023000000408000008080000040800000230000001a000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x95 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x95x3 : RowFact 7 95 ⟨false,true,true⟩ :=
  checked_row (mask:=0x10000000280000004c0000008200000043000000208000001880000006800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x95 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x95x4 : RowFact 7 95 ⟨true,false,false⟩ :=
  checked_row (mask:=0x600000009000000118000000840000008600000041000000210000001a00000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x95 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x95x5 : RowFact 7 95 ⟨true,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000820000008100000101000000860000006400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x95 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x95x6 : RowFact 7 95 ⟨true,true,false⟩ :=
  checked_row (mask:=0xc0000001200000023000000408000008080000041000000210000001a000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x95 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x95x7 : RowFact 7 95 ⟨true,true,true⟩ :=
  checked_row (mask:=0x100000002800000044000000820000004100000021000000108000000c800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x95 (by decide +kernel) (by decide +kernel)

theorem checked7x95 (g : Orientation) : RowFact 7 95 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x95x0
  · exact part7x95x1
  · exact part7x95x2
  · exact part7x95x3
  · exact part7x95x4
  · exact part7x95x5
  · exact part7x95x6
  · exact part7x95x7

private def cache7x96 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0xc000000040000000700000001)
  | ⟨false,false,true⟩ => (-94,0x40000001c000000100000003)
  | ⟨false,true,false⟩ => (0,0x6000000040000001c0000001)
  | ⟨false,true,true⟩ => (-99,0x80000000e0000000200000003)
  | ⟨true,false,false⟩ => (0,0x80000000e0000000200000003)
  | ⟨true,false,true⟩ => (-93,0x6000000040000001c0000001)
  | ⟨true,true,false⟩ => (-1,0x40000001c000000100000003)
  | ⟨true,true,true⟩ => (-99,0xc000000040000000700000001)

set_option maxRecDepth 20000 in
private theorem view7x96 (g : Orientation) : cache7x96 g=views (shape 7 96) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x96x0 : RowFact 7 96 ⟨false,false,false⟩ :=
  checked_row (mask:=0xc000000130000001080000008c0000008200000062000000210000001900000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x96 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x96x1 : RowFact 7 96 ⟨false,false,true⟩ :=
  checked_row (mask:=0x3800000044000000c6000001010000010100000082000000820000006c00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x96 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x96x2 : RowFact 7 96 ⟨false,true,false⟩ :=
  checked_row (mask:=0xc000000320000004300000040800000808000004080000043000000320000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x96 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x96x3 : RowFact 7 96 ⟨false,true,true⟩ :=
  checked_row (mask:=0x70000000880000004c0000004200000023000000208000001880000006800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x96 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x96x4 : RowFact 7 96 ⟨true,false,false⟩ :=
  checked_row (mask:=0xe00000011000000098000000840000004600000041000000310000000d00000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x96 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x96x5 : RowFact 7 96 ⟨true,false,true⟩ :=
  checked_row (mask:=0x180000006400000086000000810000010100000081000000860000006400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x96 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x96x6 : RowFact 7 96 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1c00000022000000630000008080000080800000410000004100000036000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x96 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x96x7 : RowFact 7 96 ⟨true,true,true⟩ :=
  checked_row (mask:=0x600000009800000084000000460000004100000031000000108000000c800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x96 (by decide +kernel) (by decide +kernel)

theorem checked7x96 (g : Orientation) : RowFact 7 96 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x96x0
  · exact part7x96x1
  · exact part7x96x2
  · exact part7x96x3
  · exact part7x96x4
  · exact part7x96x5
  · exact part7x96x6
  · exact part7x96x7

end HalfIndexRows
