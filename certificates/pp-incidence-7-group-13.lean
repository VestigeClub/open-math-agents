import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 49, 50, 51, 52. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x49 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x50000000700000005)
  | ⟨false,false,true⟩ => (-64,0x50000000700000005)
  | ⟨false,true,false⟩ => (-2,0x50000000700000005)
  | ⟨false,true,true⟩ => (-66,0x50000000700000005)
  | ⟨true,false,false⟩ => (0,0x70000000200000007)
  | ⟨true,false,true⟩ => (-64,0x70000000200000007)
  | ⟨true,true,false⟩ => (-2,0x70000000200000007)
  | ⟨true,true,true⟩ => (-66,0x70000000200000007)

set_option maxRecDepth 20000 in
private theorem view7x49 (g : Orientation) : cache7x49 g=views (shape 7 49) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x49x0 : RowFact 7 49 ⟨false,false,false⟩ :=
  checked_row (mask:=0x54000000aa000000820000008200000082000000aa0000005400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x49 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x49x1 : RowFact 7 49 ⟨false,false,true⟩ :=
  checked_row (mask:=0x54000000aa000000820000008200000082000000aa00000054000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x49 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x49x2 : RowFact 7 49 ⟨false,true,false⟩ :=
  checked_row (mask:=0x150000002a8000002080000020800000208000002a80000015000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x49 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x49x3 : RowFact 7 49 ⟨false,true,true⟩ :=
  checked_row (mask:=0x150000002a8000002080000020800000208000002a800000150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x49 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x49x4 : RowFact 7 49 ⟨true,false,false⟩ :=
  checked_row (mask:=0x7c00000082000000820000008200000082000000820000007c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x49 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x49x5 : RowFact 7 49 ⟨true,false,true⟩ :=
  checked_row (mask:=0x7c00000082000000820000008200000082000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x49 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x49x6 : RowFact 7 49 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1f00000020800000208000002080000020800000208000001f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x49 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x49x7 : RowFact 7 49 ⟨true,true,true⟩ :=
  checked_row (mask:=0x1f00000020800000208000002080000020800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x49 (by decide +kernel) (by decide +kernel)

theorem checked7x49 (g : Orientation) : RowFact 7 49 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x49x0
  · exact part7x49x1
  · exact part7x49x2
  · exact part7x49x3
  · exact part7x49x4
  · exact part7x49x5
  · exact part7x49x6
  · exact part7x49x7

private def cache7x50 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000070000000d)
  | ⟨false,false,true⟩ => (-64,0xd0000000700000001)
  | ⟨false,true,false⟩ => (-3,0x80000000e0000000b)
  | ⟨false,true,true⟩ => (-64,0x160000001c0000001)
  | ⟨true,false,false⟩ => (0,0x1000000030000000200000007)
  | ⟨true,false,true⟩ => (-96,0x7000000020000000300000001)
  | ⟨true,true,false⟩ => (-2,0x4000000060000000200000007)
  | ⟨true,true,true⟩ => (-96,0x1c00000008000000180000001)

set_option maxRecDepth 20000 in
private theorem view7x50 (g : Orientation) : cache7x50 g=views (shape 7 50) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x50x0 : RowFact 7 50 ⟨false,false,false⟩ :=
  checked_row (mask:=0x16000000690000008100000101000001020000012c000000d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x50 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x50x1 : RowFact 7 50 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c00000082000001010000010100000101000000fe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x50 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x50x2 : RowFact 7 50 ⟨false,true,false⟩ :=
  checked_row (mask:=0xd00000032800000408000008080000040800000328000000d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x50 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x50x3 : RowFact 7 50 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000006800000188000002080000040800000828000007d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x50 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x50x4 : RowFact 7 50 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1c000000620000008200000102000000840000010400000128000000d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x50 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x50x5 : RowFact 7 50 ⟨true,false,true⟩ :=
  checked_row (mask:=0x10000000680000008400000104000001020000008200000102000000fc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x50 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x50x6 : RowFact 7 50 ⟨true,true,false⟩ :=
  checked_row (mask:=0x70000001880000020800000408000002080000020800000128000000d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x50 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x50x7 : RowFact 7 50 ⟨true,true,true⟩ :=
  checked_row (mask:=0x10000000680000008800000108000002080000020800000408000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x50 (by decide +kernel) (by decide +kernel)

theorem checked7x50 (g : Orientation) : RowFact 7 50 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x50x0
  · exact part7x50x1
  · exact part7x50x2
  · exact part7x50x3
  · exact part7x50x4
  · exact part7x50x5
  · exact part7x50x6
  · exact part7x50x7

private def cache7x51 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x10000000f00000005)
  | ⟨false,false,true⟩ => (-64,0x50000000f00000001)
  | ⟨false,true,false⟩ => (-2,0x40000000780000005)
  | ⟨false,true,true⟩ => (-64,0x140000001e0000001)
  | ⟨true,false,false⟩ => (0,0x2000000030000000200000007)
  | ⟨true,false,true⟩ => (-95,0x3800000010000000180000001)
  | ⟨true,true,false⟩ => (-2,0x2000000060000000200000007)
  | ⟨true,true,true⟩ => (-97,0x3800000010000000300000001)

set_option maxRecDepth 20000 in
private theorem view7x51 (g : Orientation) : cache7x51 g=views (shape 7 51) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x51x0 : RowFact 7 51 ⟨false,false,false⟩ :=
  checked_row (mask:=0x14000000ea000001010000010100000101000000ae0000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x51 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x51x1 : RowFact 7 51 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000ee000001010000010100000101000000aa00000054000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x51 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x51x2 : RowFact 7 51 ⟨false,true,false⟩ :=
  checked_row (mask:=0x50000003a8000004080000080800000408000003a80000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x51 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x51x3 : RowFact 7 51 ⟨false,true,true⟩ :=
  checked_row (mask:=0x10000000e8000007080000080800000408000002a800000150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x51 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x51x4 : RowFact 7 51 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1c000000e2000001020000008200000104000000840000005400000028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x51 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x51x5 : RowFact 7 51 ⟨true,false,true⟩ :=
  checked_row (mask:=0x80000007400000084000001040000008200000102000000820000007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x51 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x51x6 : RowFact 7 51 ⟨true,true,false⟩ :=
  checked_row (mask:=0x70000003880000040800000208000002080000020800000150000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x51 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x51x7 : RowFact 7 51 ⟨true,true,true⟩ :=
  checked_row (mask:=0x20000001d00000020800000208000002080000040800000208000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x51 (by decide +kernel) (by decide +kernel)

theorem checked7x51 (g : Orientation) : RowFact 7 51 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x51x0
  · exact part7x51x1
  · exact part7x51x2
  · exact part7x51x3
  · exact part7x51x4
  · exact part7x51x5
  · exact part7x51x6
  · exact part7x51x7

private def cache7x52 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x4000000050000000700000001)
  | ⟨false,false,true⟩ => (-94,0x40000001c000000140000001)
  | ⟨false,true,false⟩ => (0,0x4000000140000001c0000001)
  | ⟨false,true,true⟩ => (-98,0x4000000070000000500000001)
  | ⟨true,false,false⟩ => (0,0xe0000000200000007)
  | ⟨true,false,true⟩ => (-63,0x38000000100000007)
  | ⟨true,true,false⟩ => (-2,0x38000000200000007)
  | ⟨true,true,true⟩ => (-67,0xe0000000400000007)

set_option maxRecDepth 20000 in
private theorem view7x52 (g : Orientation) : cache7x52 g=views (shape 7 52) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x52x0 : RowFact 7 52 ⟨false,false,false⟩ :=
  checked_row (mask:=0x40000000b00000008c000000820000008200000082000000620000001a00000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x52 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x52x1 : RowFact 7 52 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c000000aa000000820000008200000082000000820000006c00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x52 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x52x2 : RowFact 7 52 ⟨false,true,false⟩ :=
  checked_row (mask:=0x40000001b00000022800000208000002080000020800000228000001b000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x52 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x52x3 : RowFact 7 52 ⟨false,true,true⟩ :=
  checked_row (mask:=0x100000002c0000002b0000002280000020800000208000001880000006800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x52 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x52x4 : RowFact 7 52 ⟨true,false,false⟩ :=
  checked_row (mask:=0x700000008c00000082000000820000004100000041000000310000000e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x52 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x52x5 : RowFact 7 52 ⟨true,false,true⟩ :=
  checked_row (mask:=0x380000004600000041000000810000008100000082000000620000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x52 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x52x6 : RowFact 7 52 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1c0000002300000020800000408000004080000041000000310000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x52 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x52x7 : RowFact 7 52 ⟨true,true,true⟩ :=
  checked_row (mask:=0x38000000460000004100000041000000208000002080000018800000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x52 (by decide +kernel) (by decide +kernel)

theorem checked7x52 (g : Orientation) : RowFact 7 52 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x52x0
  · exact part7x52x1
  · exact part7x52x2
  · exact part7x52x3
  · exact part7x52x4
  · exact part7x52x5
  · exact part7x52x6
  · exact part7x52x7

end HalfIndexRows
