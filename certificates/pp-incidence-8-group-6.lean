import certificates.«pp-incidence-rows-core»

/-! All placements for free 8-cell tile indices 63, 65, 66, 67. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache8x63 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000030000000500000007)
  | ⟨false,false,true⟩ => (-96,0x7000000050000000300000001)
  | ⟨false,true,false⟩ => (-2,0x4000000060000000500000007)
  | ⟨false,true,true⟩ => (-96,0x1c00000014000000180000001)
  | ⟨true,false,false⟩ => (0,0x3000000050000000f)
  | ⟨true,false,true⟩ => (-64,0xf0000000500000003)
  | ⟨true,true,false⟩ => (-3,0xc0000000a0000000f)
  | ⟨true,true,true⟩ => (-65,0x3c000000280000003)

set_option maxRecDepth 20000 in
private theorem view8x63 (g : Orientation) : cache8x63 g=views (shape 8 63) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x63x0 : RowFact 8 63 ⟨false,false,false⟩ :=
  checked_row (mask:=0x1c0000002200000042000000820000008200000082000000840000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x63 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x63x1 : RowFact 8 63 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000280000004400000082000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x63 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x63x2 : RowFact 8 63 ⟨false,true,false⟩ :=
  checked_row (mask:=0x700000008800000108000002080000020800000208000001080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x63 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x63x3 : RowFact 8 63 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1000000028000000480000008800000108000002080000020800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x63 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x63x4 : RowFact 8 63 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e0000002100000041000000810000008100000082000000840000007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x63 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x63x5 : RowFact 8 63 ⟨true,false,true⟩ :=
  checked_row (mask:=0x180000002400000042000000810000008100000081000000810000007e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x63 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x63x6 : RowFact 8 63 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf0000001080000020800000408000004080000020800000108000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x63 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x63x7 : RowFact 8 63 ⟨true,true,true⟩ :=
  checked_row (mask:=0x30000000480000008800000108000002080000040800000408000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x63 (by decide +kernel) (by decide +kernel)

theorem checked8x63 (g : Orientation) : RowFact 8 63 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x63x0
  · exact part8x63x1
  · exact part8x63x2
  · exact part8x63x3
  · exact part8x63x4
  · exact part8x63x5
  · exact part8x63x6
  · exact part8x63x7

private def cache8x65 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x100000003000000010000000f)
  | ⟨false,false,true⟩ => (-96,0xf000000010000000300000001)
  | ⟨false,true,false⟩ => (-3,0x80000000c000000080000000f)
  | ⟨false,true,true⟩ => (-96,0x1e00000010000000180000001)
  | ⟨true,false,false⟩ => (0,0x100000001000000050000000f)
  | ⟨true,false,true⟩ => (-96,0xf000000050000000100000001)
  | ⟨true,true,false⟩ => (-3,0x8000000080000000a0000000f)
  | ⟨true,true,true⟩ => (-96,0x1e00000014000000100000001)

set_option maxRecDepth 20000 in
private theorem view8x65 (g : Orientation) : cache8x65 g=views (shape 8 65) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x65x0 : RowFact 8 65 ⟨false,false,false⟩ :=
  checked_row (mask:=0x1e0000002100000041000000c100000101000001060000010400000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x65 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x65x1 : RowFact 8 65 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000c600000101000001010000010100000101000000fe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x65 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x65x2 : RowFact 8 65 ⟨false,true,false⟩ :=
  checked_row (mask:=0xf000000108000002080000070800000808000007080000020800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x65 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x65x3 : RowFact 8 65 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1000000028000000480000008800000108000002080000070800000808000007f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x65 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x65x4 : RowFact 8 65 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e0000002100000041000000c100000101000001020000010c00000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x65 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x65x5 : RowFact 8 65 ⟨true,false,true⟩ :=
  checked_row (mask:=0x10000000280000004c000000ca00000101000001010000010100000101000000fe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x65 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x65x6 : RowFact 8 65 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf000000108000002080000070800000808000004080000030800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x65 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x65x7 : RowFact 8 65 ⟨true,true,true⟩ :=
  checked_row (mask:=0x1000000028000000480000008800000108000002080000040800000808000007f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x65 (by decide +kernel) (by decide +kernel)

theorem checked8x65 (g : Orientation) : RowFact 8 65 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x65x0
  · exact part8x65x1
  · exact part8x65x2
  · exact part8x65x3
  · exact part8x65x4
  · exact part8x65x5
  · exact part8x65x6
  · exact part8x65x7

private def cache8x66 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000070000000500000003)
  | ⟨false,false,true⟩ => (-96,0x3000000050000000700000001)
  | ⟨false,true,false⟩ => (-1,0x2000000038000000280000003)
  | ⟨false,true,true⟩ => (-96,0x18000000140000001c0000001)
  | ⟨true,false,false⟩ => (0,0x6000000050000000f)
  | ⟨true,false,true⟩ => (-63,0x78000000280000003)
  | ⟨true,true,false⟩ => (-3,0x60000000a0000000f)
  | ⟨true,true,true⟩ => (-66,0x78000000500000003)

set_option maxRecDepth 20000 in
private theorem view8x66 (g : Orientation) : cache8x66 g=views (shape 8 66) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x66x0 : RowFact 8 66 ⟨false,false,false⟩ :=
  checked_row (mask:=0x180000006400000082000000820000008200000082000000820000004c00000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x66 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x66x1 : RowFact 8 66 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c00000082000000820000008200000082000000820000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x66 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x66x2 : RowFact 8 66 ⟨false,true,false⟩ :=
  checked_row (mask:=0x30000000c80000010800000208000002080000020800000108000000c800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x66 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x66x3 : RowFact 8 66 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000006800000188000002080000020800000208000001080000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x66 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x66x4 : RowFact 8 66 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e0000006100000081000000810000008100000042000000220000001c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x66 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x66x5 : RowFact 8 66 ⟨true,false,true⟩ :=
  checked_row (mask:=0xc0000003200000042000000810000008100000081000000410000003e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x66 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x66x6 : RowFact 8 66 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf0000003080000040800000408000002080000020800000110000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x66 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x66x7 : RowFact 8 66 ⟨true,true,true⟩ :=
  checked_row (mask:=0x60000001900000020800000208000004080000040800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x66 (by decide +kernel) (by decide +kernel)

theorem checked8x66 (g : Orientation) : RowFact 8 66 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x66x0
  · exact part8x66x1
  · exact part8x66x2
  · exact part8x66x3
  · exact part8x66x4
  · exact part8x66x5
  · exact part8x66x6
  · exact part8x66x7

private def cache8x67 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x5000000070000000100000003)
  | ⟨false,false,true⟩ => (-96,0x3000000010000000700000005)
  | ⟨false,true,false⟩ => (-1,0x2800000038000000200000003)
  | ⟨false,true,true⟩ => (-98,0x6000000040000000700000005)
  | ⟨true,false,false⟩ => (0,0xc000000050000000f)
  | ⟨true,false,true⟩ => (-62,0x3c000000140000003)
  | ⟨true,true,false⟩ => (-3,0x30000000a0000000f)
  | ⟨true,true,true⟩ => (-67,0xf0000000a00000003)

set_option maxRecDepth 20000 in
private theorem view8x67 (g : Orientation) : cache8x67 g=views (shape 8 67) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x67x0 : RowFact 8 67 ⟨false,false,false⟩ :=
  checked_row (mask:=0x78000000840000008400000082000000820000008200000042000000420000003c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x67 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x67x1 : RowFact 8 67 ⟨false,false,true⟩ :=
  checked_row (mask:=0x54000000aa00000082000000820000008200000082000000440000004400000038000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x67 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x67x2 : RowFact 8 67 ⟨false,true,false⟩ :=
  checked_row (mask:=0xf000000108000001080000020800000208000002080000010800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x67 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x67x3 : RowFact 8 67 ⟨false,true,true⟩ :=
  checked_row (mask:=0x150000002a800000208000002080000010800000108000000c80000008800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x67 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x67x4 : RowFact 8 67 ⟨true,false,false⟩ :=
  checked_row (mask:=0x7e0000008100000081000000810000004100000041000000310000000e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x67 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x67x5 : RowFact 8 67 ⟨true,false,true⟩ :=
  checked_row (mask:=0x1e00000061000000a1000000810000008100000041000000410000003e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x67 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x67x6 : RowFact 8 67 ⟨true,true,false⟩ :=
  checked_row (mask:=0x3f0000004080000040800000408000004080000030800000230000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x67 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part8x67x7 : RowFact 8 67 ⟨true,true,true⟩ :=
  checked_row (mask:=0x3c0000004300000042800000408000004080000030800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view8x67 (by decide +kernel) (by decide +kernel)

theorem checked8x67 (g : Orientation) : RowFact 8 67 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part8x67x0
  · exact part8x67x1
  · exact part8x67x2
  · exact part8x67x3
  · exact part8x67x4
  · exact part8x67x5
  · exact part8x67x6
  · exact part8x67x7

end HalfIndexRows
