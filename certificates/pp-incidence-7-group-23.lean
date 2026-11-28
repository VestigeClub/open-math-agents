import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 89, 90, 91, 92. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x89 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x20000001f00000001)
  | ⟨false,false,true⟩ => (-63,0x8000000f80000001)
  | ⟨false,true,false⟩ => (0,0x80000001f0000001)
  | ⟨false,true,true⟩ => (-65,0x200000003e0000001)
  | ⟨true,false,false⟩ => (0,0x200000002000000020000000600000003)
  | ⟨true,false,true⟩ => (-127,0x180000003000000010000000100000001)
  | ⟨true,true,false⟩ => (-1,0x100000001000000010000000180000003)
  | ⟨true,true,true⟩ => (-129,0x300000001800000010000000100000001)

set_option maxRecDepth 20000 in
private theorem view7x89 (g : Orientation) : cache7x89 g=views (shape 7 89) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x89x0 : RowFact 7 89 ⟨false,false,false⟩ :=
  checked_row (mask:=0x20000001de000002010000020080000100800000f70000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x89 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x89x1 : RowFact 7 89 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000ee000001010000020080000200800001ef00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x89 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x89x2 : RowFact 7 89 ⟨false,true,false⟩ :=
  checked_row (mask:=0x20000003d000001c080000200800001c08000003d00000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x89 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x89x3 : RowFact 7 89 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000003a000001c100000200800001e08000001e800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x89 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x89x4 : RowFact 7 89 ⟨true,false,false⟩ :=
  checked_row (mask:=0x30000001c80000020400000102000001020000010400000104000000f4000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x89 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x89x5 : RowFact 7 89 ⟨true,false,true⟩ :=
  checked_row (mask:=0x10000000e80000010400000104000001040000010200000202000001e400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x89 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x89x6 : RowFact 7 89 ⟨true,true,false⟩ :=
  checked_row (mask:=0x60000003900000040800000808000004100000041000000410000003d0000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x89 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x89x7 : RowFact 7 89 ⟨true,true,true⟩ :=
  checked_row (mask:=0x40000003a00000041000000410000004100000081000000408000003c800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x89 (by decide +kernel) (by decide +kernel)

theorem checked7x89 (g : Orientation) : RowFact 7 89 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x89x0
  · exact part7x89x1
  · exact part7x89x2
  · exact part7x89x3
  · exact part7x89x4
  · exact part7x89x5
  · exact part7x89x6
  · exact part7x89x7

private def cache7x90 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x40000000e0000000300000001)
  | ⟨false,false,true⟩ => (-94,0x40000000c000000380000001)
  | ⟨false,true,false⟩ => (0,0x40000000e000000180000001)
  | ⟨false,true,true⟩ => (-98,0x4000000060000000380000001)
  | ⟨true,false,false⟩ => (0,0x40000000c0000000600000003)
  | ⟨true,false,true⟩ => (-94,0xc00000018000000300000001)
  | ⟨true,true,false⟩ => (-1,0x80000000c000000180000003)
  | ⟨true,true,true⟩ => (-98,0x6000000030000000180000001)

set_option maxRecDepth 20000 in
private theorem view7x90 (g : Orientation) : cache7x90 g=views (shape 7 90) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x90x0 : RowFact 7 90 ⟨false,false,false⟩ :=
  checked_row (mask:=0x40000000a000000118000001040000008200000041000000310000000a00000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x90 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x90x1 : RowFact 7 90 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000820000010100000101000000c60000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x90 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x90x2 : RowFact 7 90 ⟨false,true,false⟩ :=
  checked_row (mask:=0x40000000a00000031000000408000008080000040800000310000000a000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x90 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x90x3 : RowFact 7 90 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1000000028000000440000008200000061000000108000000c80000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x90 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x90x4 : RowFact 7 90 ⟨true,false,false⟩ :=
  checked_row (mask:=0x600000009000000108000000840000004200000041000000310000000a00000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x90 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x90x5 : RowFact 7 90 ⟨true,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000420000008100000101000000c20000002400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x90 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x90x6 : RowFact 7 90 ⟨true,true,false⟩ :=
  checked_row (mask:=0xc0000001200000021000000408000008080000041000000320000000a000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x90 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x90x7 : RowFact 7 90 ⟨true,true,true⟩ :=
  checked_row (mask:=0x1000000028000000440000008200000042000000210000001880000004800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x90 (by decide +kernel) (by decide +kernel)

theorem checked7x90 (g : Orientation) : RowFact 7 90 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x90x0
  · exact part7x90x1
  · exact part7x90x2
  · exact part7x90x3
  · exact part7x90x4
  · exact part7x90x5
  · exact part7x90x6
  · exact part7x90x7

private def cache7x91 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0xc000000060000000300000001)
  | ⟨false,false,true⟩ => (-94,0x40000000c000000180000003)
  | ⟨false,true,false⟩ => (0,0x60000000c000000180000001)
  | ⟨false,true,true⟩ => (-99,0x80000000c0000000600000003)
  | ⟨true,false,false⟩ => (0,0x80000000c0000000600000003)
  | ⟨true,false,true⟩ => (-93,0x60000000c000000180000001)
  | ⟨true,true,false⟩ => (-1,0x40000000c000000180000003)
  | ⟨true,true,true⟩ => (-99,0xc000000060000000300000001)

set_option maxRecDepth 20000 in
private theorem view7x91 (g : Orientation) : cache7x91 g=views (shape 7 91) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x91x0 : RowFact 7 91 ⟨false,false,false⟩ :=
  checked_row (mask:=0xc00000012000000110000000880000004400000022000000110000000900000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x91 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x91x1 : RowFact 7 91 ⟨false,false,true⟩ :=
  checked_row (mask:=0x380000004400000082000001010000010100000082000000440000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x91 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x91x2 : RowFact 7 91 ⟨false,true,false⟩ :=
  checked_row (mask:=0xc000000120000002100000040800000808000004080000021000000120000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x91 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x91x3 : RowFact 7 91 ⟨false,true,true⟩ :=
  checked_row (mask:=0x7000000088000000440000002200000011000000088000000480000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x91 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x91x4 : RowFact 7 91 ⟨true,false,false⟩ :=
  checked_row (mask:=0xe00000011000000088000000440000002200000011000000090000000500000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x91 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x91x5 : RowFact 7 91 ⟨true,false,true⟩ :=
  checked_row (mask:=0x180000002400000042000000810000010100000081000000420000002400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x91 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x91x6 : RowFact 7 91 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1c00000022000000410000008080000080800000410000002200000014000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x91 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x91x7 : RowFact 7 91 ⟨true,true,true⟩ :=
  checked_row (mask:=0x6000000090000000880000004400000022000000110000000880000004800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x91 (by decide +kernel) (by decide +kernel)

theorem checked7x91 (g : Orientation) : RowFact 7 91 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x91x0
  · exact part7x91x1
  · exact part7x91x2
  · exact part7x91x3
  · exact part7x91x4
  · exact part7x91x5
  · exact part7x91x6
  · exact part7x91x7

private def cache7x92 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x80000000e0000000300000001)
  | ⟨false,false,true⟩ => (-93,0x2000000060000001c0000001)
  | ⟨false,true,false⟩ => (0,0x20000000e000000180000001)
  | ⟨false,true,true⟩ => (-99,0x80000000c0000000700000001)
  | ⟨true,false,false⟩ => (0,0xc000000040000000600000003)
  | ⟨true,false,true⟩ => (-94,0xc00000018000000100000003)
  | ⟨true,true,false⟩ => (-1,0xc00000008000000180000003)
  | ⟨true,true,true⟩ => (-99,0xc000000060000000200000003)

set_option maxRecDepth 20000 in
private theorem view7x92 (g : Orientation) : cache7x92 g=views (shape 7 92) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x92x0 : RowFact 7 92 ⟨false,false,false⟩ :=
  checked_row (mask:=0x8000000160000001100000010c0000008200000061000000110000000d00000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x92 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x92x1 : RowFact 7 92 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c00000082000001010000010100000101000000c60000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x92 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x92x2 : RowFact 7 92 ⟨false,true,false⟩ :=
  checked_row (mask:=0x800000016000000610000008080000080800000808000006100000016000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x92 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x92x3 : RowFact 7 92 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000b00000008c0000008200000061000000108000000c80000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x92 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x92x4 : RowFact 7 92 ⟨true,false,false⟩ :=
  checked_row (mask:=0xc00000013000000108000000840000004200000042000000310000000900000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x92 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x92x5 : RowFact 7 92 ⟨true,false,true⟩ :=
  checked_row (mask:=0x300000004c00000042000000810000010100000102000000c20000002400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x92 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x92x6 : RowFact 7 92 ⟨true,true,false⟩ :=
  checked_row (mask:=0x18000000260000004100000040800000808000008100000062000000120000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x92 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x92x7 : RowFact 7 92 ⟨true,true,true⟩ :=
  checked_row (mask:=0x6000000098000000840000004200000042000000210000001880000004800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x92 (by decide +kernel) (by decide +kernel)

theorem checked7x92 (g : Orientation) : RowFact 7 92 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x92x0
  · exact part7x92x1
  · exact part7x92x2
  · exact part7x92x3
  · exact part7x92x4
  · exact part7x92x5
  · exact part7x92x6
  · exact part7x92x7

end HalfIndexRows
