import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 25, 26, 27, 28. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x25 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x200000003000000010000000300000001)
  | ⟨false,false,true⟩ => (-127,0x80000001800000008000000180000001)
  | ⟨false,true,false⟩ => (0,0x80000001800000010000000180000001)
  | ⟨false,true,true⟩ => (-129,0x200000003000000020000000300000001)
  | ⟨true,false,false⟩ => (0,0x1a0000000f)
  | ⟨true,false,true⟩ => (-31,0x78000000d)
  | ⟨true,true,false⟩ => (-3,0x58000000f)
  | ⟨true,true,true⟩ => (-36,0x1e0000000b)

set_option maxRecDepth 20000 in
private theorem view7x25 (g : Orientation) : cache7x25 g=views (shape 7 25) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x25x0 : RowFact 7 25 ⟨false,false,false⟩ :=
  checked_row (mask:=0x20000000500000004800000044000000440000004400000044000000440000002400000014000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x25 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x25x1 : RowFact 7 25 ⟨false,false,true⟩ :=
  checked_row (mask:=0x1000000028000000440000004400000044000000440000004400000044000000440000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x25 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x25x2 : RowFact 7 25 ⟨false,true,false⟩ :=
  checked_row (mask:=0x20000000500000008800000088000000880000008800000088000000880000008800000050000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x25 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x25x3 : RowFact 7 25 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000000a0000000900000008800000088000000880000004800000088000000480000002800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x25 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x25x4 : RowFact 7 25 ⟨true,false,false⟩ :=
  checked_row (mask:=0x3c0000004200000041000000208000004080000020800000148000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x25 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x25x5 : RowFact 7 25 ⟨true,false,true⟩ :=
  checked_row (mask:=0x160000002900000040800000408000002080000040800000210000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x25 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x25x6 : RowFact 7 25 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1e0000002100000040800000408000002080000040800000250000001a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x25 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x25x7 : RowFact 7 25 ⟨true,true,true⟩ :=
  checked_row (mask:=0x340000004a00000041000000208000004080000020800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x25 (by decide +kernel) (by decide +kernel)

theorem checked7x25 (g : Orientation) : RowFact 7 25 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x25x0
  · exact part7x25x1
  · exact part7x25x2
  · exact part7x25x3
  · exact part7x25x4
  · exact part7x25x5
  · exact part7x25x6
  · exact part7x25x7

private def cache7x26 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000010000000700000005)
  | ⟨false,false,true⟩ => (-96,0x5000000070000000100000001)
  | ⟨false,true,false⟩ => (-2,0x4000000040000000700000005)
  | ⟨false,true,true⟩ => (-96,0x140000001c000000100000001)
  | ⟨true,false,false⟩ => (0,0x3000000020000000f)
  | ⟨true,false,true⟩ => (-64,0xf0000000200000003)
  | ⟨true,true,false⟩ => (-3,0xc000000040000000f)
  | ⟨true,true,true⟩ => (-65,0x3c000000100000003)

set_option maxRecDepth 20000 in
private theorem view7x26 (g : Orientation) : cache7x26 g=views (shape 7 26) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x26x0 : RowFact 7 26 ⟨false,false,false⟩ :=
  checked_row (mask:=0x140000002a000000620000008200000082000000820000008c000000a800000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x26 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x26x1 : RowFact 7 26 ⟨false,false,true⟩ :=
  checked_row (mask:=0x10000000280000006c00000082000000820000008200000082000000aa00000054000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x26 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x26x2 : RowFact 7 26 ⟨false,true,false⟩ :=
  checked_row (mask:=0x50000000a80000018800000208000002080000020800000188000000a800000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x26 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x26x3 : RowFact 7 26 ⟨false,true,true⟩ :=
  checked_row (mask:=0x10000000280000006800000088000001880000020800000208000002a800000150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x26 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x26x4 : RowFact 7 26 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e0000002100000061000000810000008100000086000000840000007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x26 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x26x5 : RowFact 7 26 ⟨true,false,true⟩ :=
  checked_row (mask:=0x180000002400000066000000810000008100000081000000810000007e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x26 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x26x6 : RowFact 7 26 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf0000001080000030800000408000004080000030800000108000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x26 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x26x7 : RowFact 7 26 ⟨true,true,true⟩ :=
  checked_row (mask:=0x3000000048000000c800000108000003080000040800000408000003f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x26 (by decide +kernel) (by decide +kernel)

theorem checked7x26 (g : Orientation) : RowFact 7 26 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x26x0
  · exact part7x26x1
  · exact part7x26x2
  · exact part7x26x3
  · exact part7x26x4
  · exact part7x26x5
  · exact part7x26x6
  · exact part7x26x7

private def cache7x27 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000050000000700000001)
  | ⟨false,false,true⟩ => (-96,0x1000000070000000500000001)
  | ⟨false,true,false⟩ => (0,0x10000000140000001c0000001)
  | ⟨false,true,true⟩ => (-96,0x100000001c000000140000001)
  | ⟨true,false,false⟩ => (0,0x6000000020000000f)
  | ⟨true,false,true⟩ => (-63,0x78000000100000003)
  | ⟨true,true,false⟩ => (-3,0x6000000040000000f)
  | ⟨true,true,true⟩ => (-66,0x78000000200000003)

set_option maxRecDepth 20000 in
private theorem view7x27 (g : Orientation) : cache7x27 g=views (shape 7 27) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x27x0 : RowFact 7 27 ⟨false,false,false⟩ :=
  checked_row (mask:=0x100000006c000000a20000008200000082000000820000008a0000006c00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x27 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x27x1 : RowFact 7 27 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c000000aa000000820000008200000082000000820000006c00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x27 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x27x2 : RowFact 7 27 ⟨false,true,false⟩ :=
  checked_row (mask:=0x100000006800000188000002080000020800000208000001880000006800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x27 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x27x3 : RowFact 7 27 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1000000068000001a8000002880000020800000208000001880000006800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x27 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x27x4 : RowFact 7 27 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e0000006100000081000000810000004100000042000000320000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x27 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x27x5 : RowFact 7 27 ⟨true,false,true⟩ :=
  checked_row (mask:=0xc0000003200000042000000410000008100000081000000610000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x27 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x27x6 : RowFact 7 27 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf00000030800000408000004080000020800000210000001900000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x27 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x27x7 : RowFact 7 27 ⟨true,true,true⟩ :=
  checked_row (mask:=0x60000001900000021000000208000004080000040800000308000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x27 (by decide +kernel) (by decide +kernel)

theorem checked7x27 (g : Orientation) : RowFact 7 27 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x27x0
  · exact part7x27x1
  · exact part7x27x2
  · exact part7x27x3
  · exact part7x27x4
  · exact part7x27x5
  · exact part7x27x6
  · exact part7x27x7

private def cache7x28 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x1000000010000000f00000001)
  | ⟨false,false,true⟩ => (-96,0x10000000f0000000100000001)
  | ⟨false,true,false⟩ => (0,0x10000000100000001e0000001)
  | ⟨false,true,true⟩ => (-96,0x100000001e000000100000001)
  | ⟨true,false,false⟩ => (0,0x200000002000000020000000f)
  | ⟨true,false,true⟩ => (-95,0x7800000010000000100000001)
  | ⟨true,true,false⟩ => (-3,0x400000004000000040000000f)
  | ⟨true,true,true⟩ => (-97,0x3c00000010000000100000001)

set_option maxRecDepth 20000 in
private theorem view7x28 (g : Orientation) : cache7x28 g=views (shape 7 28) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x28x0 : RowFact 7 28 ⟨false,false,false⟩ :=
  checked_row (mask:=0x100000002e000000e10000010100000101000001010000010e000000e800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x28 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x28x1 : RowFact 7 28 ⟨false,false,true⟩ :=
  checked_row (mask:=0x1000000028000000ee00000101000001010000010100000101000000ee00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x28 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x28x2 : RowFact 7 28 ⟨false,true,false⟩ :=
  checked_row (mask:=0x10000000e80000010800000708000008080000070800000108000000e800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x28 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x28x3 : RowFact 7 28 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1000000028000000e800000108000007080000080800000708000000e800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x28 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x28x4 : RowFact 7 28 ⟨true,false,false⟩ :=
  checked_row (mask:=0x1e00000021000000e1000001010000008100000086000000840000007400000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x28 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x28x5 : RowFact 7 28 ⟨true,false,true⟩ :=
  checked_row (mask:=0x8000000140000007400000086000000810000008100000101000000e10000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x28 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x28x6 : RowFact 7 28 ⟨true,true,false⟩ :=
  checked_row (mask:=0xf0000001080000070800000808000006080000021000000210000001d000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x28 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x28x7 : RowFact 7 28 ⟨true,true,true⟩ :=
  checked_row (mask:=0x2000000050000001d00000021000000208000006080000080800000708000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x28 (by decide +kernel) (by decide +kernel)

theorem checked7x28 (g : Orientation) : RowFact 7 28 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x28x0
  · exact part7x28x1
  · exact part7x28x2
  · exact part7x28x3
  · exact part7x28x4
  · exact part7x28x5
  · exact part7x28x6
  · exact part7x28x7

end HalfIndexRows
