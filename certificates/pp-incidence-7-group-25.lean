import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 97, 98, 99, 100. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x97 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x40000001f00000001)
  | ⟨false,false,true⟩ => (-62,0x40000007c0000001)
  | ⟨false,true,false⟩ => (0,0x40000001f0000001)
  | ⟨false,true,true⟩ => (-66,0x400000007c0000001)
  | ⟨true,false,false⟩ => (0,0x200000002000000060000000200000003)
  | ⟨true,false,true⟩ => (-127,0x180000001000000030000000100000001)
  | ⟨true,true,false⟩ => (-1,0x100000001000000018000000100000003)
  | ⟨true,true,true⟩ => (-129,0x300000001000000018000000100000001)

set_option maxRecDepth 20000 in
private theorem view7x97 (g : Orientation) : cache7x97 g=views (shape 7 97) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x97x0 : RowFact 7 97 ⟨false,false,false⟩ :=
  checked_row (mask:=0x40000001bc0000020300000200800001808000007b0000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x97 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x97x1 : RowFact 7 97 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c000001830000020080000200800001ef00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x97 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x97x2 : RowFact 7 97 ⟨false,true,false⟩ :=
  checked_row (mask:=0x40000007b0000018080000200800001808000007b00000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x97 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x97x3 : RowFact 7 97 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000006c0000018300000200800001e08000001e800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x97 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x97x4 : RowFact 7 97 ⟨true,false,false⟩ :=
  checked_row (mask:=0x60000001980000020400000104000001020000010200000104000000f4000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x97 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x97x5 : RowFact 7 97 ⟨true,false,true⟩ :=
  checked_row (mask:=0x20000000d80000010400000104000001020000010200000204000001e400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x97 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x97x6 : RowFact 7 97 ⟨true,true,false⟩ :=
  checked_row (mask:=0xc0000003300000040800000408000008100000041000000410000003d0000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x97 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x97x7 : RowFact 7 97 ⟨true,true,true⟩ :=
  checked_row (mask:=0x80000003600000041000000410000008100000041000000408000003c800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x97 (by decide +kernel) (by decide +kernel)

theorem checked7x97 (g : Orientation) : RowFact 7 97 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x97x0
  · exact part7x97x1
  · exact part7x97x2
  · exact part7x97x3
  · exact part7x97x4
  · exact part7x97x5
  · exact part7x97x6
  · exact part7x97x7

private def cache7x98 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x80000001f00000001)
  | ⟨false,false,true⟩ => (-61,0x20000003e0000001)
  | ⟨false,true,false⟩ => (0,0x20000001f0000001)
  | ⟨false,true,true⟩ => (-67,0x80000000f80000001)
  | ⟨true,false,false⟩ => (0,0x200000006000000020000000200000003)
  | ⟨true,false,true⟩ => (-127,0x180000001000000010000000300000001)
  | ⟨true,true,false⟩ => (-1,0x100000001800000010000000100000003)
  | ⟨true,true,true⟩ => (-129,0x300000001000000010000000180000001)

set_option maxRecDepth 20000 in
private theorem view7x98 (g : Orientation) : cache7x98 g=views (shape 7 98) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x98x0 : RowFact 7 98 ⟨false,false,false⟩ :=
  checked_row (mask:=0x80000001780000020700000200800001c08000003d0000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x98 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x98x1 : RowFact 7 98 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000ee000001010000020080000200800001ef00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x98 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x98x2 : RowFact 7 98 ⟨false,true,false⟩ :=
  checked_row (mask:=0x8000000f7000001008000020080000100800000f700000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x98 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x98x3 : RowFact 7 98 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000b80000010700000200800001e08000001e800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x98 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x98x4 : RowFact 7 98 ⟨true,false,false⟩ :=
  checked_row (mask:=0xc0000001380000020400000104000001040000010200000102000000f4000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x98 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x98x5 : RowFact 7 98 ⟨true,false,true⟩ :=
  checked_row (mask:=0x40000000b80000010400000102000001020000010400000204000001e400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x98 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x98x6 : RowFact 7 98 ⟨true,true,false⟩ :=
  checked_row (mask:=0x180000002700000040800000408000004100000081000000410000003d0000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x98 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x98x7 : RowFact 7 98 ⟨true,true,true⟩ :=
  checked_row (mask:=0x100000002e00000041000000810000004100000041000000408000003c800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x98 (by decide +kernel) (by decide +kernel)

theorem checked7x98 (g : Orientation) : RowFact 7 98 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x98x0
  · exact part7x98x1
  · exact part7x98x2
  · exact part7x98x3
  · exact part7x98x4
  · exact part7x98x5
  · exact part7x98x6
  · exact part7x98x7

private def cache7x99 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x100000001f00000001)
  | ⟨false,false,true⟩ => (-60,0x10000001f0000001)
  | ⟨false,true,false⟩ => (0,0x10000001f0000001)
  | ⟨false,true,true⟩ => (-68,0x100000001f00000001)
  | ⟨true,false,false⟩ => (0,0x600000002000000020000000200000003)
  | ⟨true,false,true⟩ => (-127,0x180000001000000010000000100000003)
  | ⟨true,true,false⟩ => (-1,0x180000001000000010000000100000003)
  | ⟨true,true,true⟩ => (-130,0x600000002000000020000000200000003)

set_option maxRecDepth 20000 in
private theorem view7x99 (g : Orientation) : cache7x99 g=views (shape 7 99) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x99x0 : RowFact 7 99 ⟨false,false,false⟩ :=
  checked_row (mask:=0x100000002f00000020f00000200800001e08000001e8000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x99 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x99x1 : RowFact 7 99 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000001ef000002008000020080000200800001ef00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x99 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x99x2 : RowFact 7 99 ⟨false,true,false⟩ :=
  checked_row (mask:=0x10000001ef000002008000020080000200800001ef00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x99 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x99x3 : RowFact 7 99 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000002f00000020f00000200800001e08000001e800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x99 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x99x4 : RowFact 7 99 ⟨true,false,false⟩ :=
  checked_row (mask:=0x180000002780000020400000104000001040000010400000102000000f20000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x99 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x99x5 : RowFact 7 99 ⟨true,false,true⟩ :=
  checked_row (mask:=0xc00000013c0000010200000102000001040000020400000204000001e400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x99 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x99x6 : RowFact 7 99 ⟨true,true,false⟩ :=
  checked_row (mask:=0x300000004f0000004080000040800000410000008100000081000000790000000600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x99 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x99x7 : RowFact 7 99 ⟨true,true,true⟩ :=
  checked_row (mask:=0x600000009e00000081000000410000004100000041000000408000003c800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x99 (by decide +kernel) (by decide +kernel)

theorem checked7x99 (g : Orientation) : RowFact 7 99 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x99x0
  · exact part7x99x1
  · exact part7x99x2
  · exact part7x99x3
  · exact part7x99x4
  · exact part7x99x5
  · exact part7x99x6
  · exact part7x99x7

private def cache7x100 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (1,0x1000000018000000380000001)
  | ⟨false,false,true⟩ => (-95,0x1000000038000000180000001)
  | ⟨false,true,false⟩ => (-1,0x1000000030000000380000001)
  | ⟨false,true,true⟩ => (-97,0x1000000038000000300000001)
  | ⟨true,false,false⟩ => (1,0x10000000780000003)
  | ⟨true,false,true⟩ => (-63,0x30000000780000001)
  | ⟨true,true,false⟩ => (-2,0x20000000780000003)
  | ⟨true,true,true⟩ => (-65,0x180000003c0000001)

set_option maxRecDepth 20000 in
private theorem view7x100 (g : Orientation) : cache7x100 g=views (shape 7 100) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x100x0 : RowFact 7 100 ⟨false,false,false⟩ :=
  checked_row (mask:=0x100000002800000044000000420000008200000084000000440000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x100 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x100x1 : RowFact 7 100 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000002800000044000000440000008200000082000000440000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x100 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x100x2 : RowFact 7 100 ⟨false,true,false⟩ :=
  checked_row (mask:=0x40000000a00000011000000108000002080000010800000110000000a000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x100 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x100x3 : RowFact 7 100 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a00000009000000108000001080000020800000110000000a000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x100 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x100x4 : RowFact 7 100 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1800000024000000420000004100000081000000420000002c0000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x100 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x100x5 : RowFact 7 100 ⟨true,false,true⟩ :=
  checked_row (mask:=0x100000002c000000420000004100000081000000420000002400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x100 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x100x6 : RowFact 7 100 ⟨true,true,false⟩ :=
  checked_row (mask:=0xc00000012000000210000002080000040800000210000001a00000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x100 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x100x7 : RowFact 7 100 ⟨true,true,true⟩ :=
  checked_row (mask:=0x40000001a00000021000000208000004080000021000000120000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x100 (by decide +kernel) (by decide +kernel)

theorem checked7x100 (g : Orientation) : RowFact 7 100 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x100x0
  · exact part7x100x1
  · exact part7x100x2
  · exact part7x100x3
  · exact part7x100x4
  · exact part7x100x5
  · exact part7x100x6
  · exact part7x100x7

end HalfIndexRows
