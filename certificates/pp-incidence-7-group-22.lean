import certificates.«pp-incidence-rows-core»

/-! All placements for free 7-cell tile indices 85, 86, 87, 88. -/

open OMA.S_oeis_a380455 PrimePolyFactor HalfCatalogue HalfGeometry HalfIncidence

namespace HalfIndexRows

private def cache7x85 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x20000000f00000005)
  | ⟨false,false,true⟩ => (-63,0x28000000780000001)
  | ⟨false,true,false⟩ => (-2,0x20000000780000005)
  | ⟨false,true,true⟩ => (-65,0x280000003c0000001)
  | ⟨true,false,false⟩ => (0,0x2000000030000000600000003)
  | ⟨true,false,true⟩ => (-95,0x1800000030000000180000001)
  | ⟨true,true,false⟩ => (-1,0x1000000030000000180000003)
  | ⟨true,true,true⟩ => (-97,0x3000000018000000300000001)

set_option maxRecDepth 20000 in
private theorem view7x85 (g : Orientation) : cache7x85 g=views (shape 7 85) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x85x0 : RowFact 7 85 ⟨false,false,false⟩ :=
  checked_row (mask:=0x28000000d4000001020000010100000081000000560000002800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x85 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x85x1 : RowFact 7 85 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c000000820000010100000101000000aa00000054000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x85 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x85x2 : RowFact 7 85 ⟨false,true,false⟩ :=
  checked_row (mask:=0xa00000035000000408000008080000040800000350000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x85 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x85x3 : RowFact 7 85 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000001a0000006100000080800000408000002a800000150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x85 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x85x4 : RowFact 7 85 ⟨true,false,false⟩ :=
  checked_row (mask:=0x30000000c8000001040000008200000102000000840000005400000028000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x85 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x85x5 : RowFact 7 85 ⟨true,false,true⟩ :=
  checked_row (mask:=0x1000000068000000840000010400000082000001020000008400000078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x85 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x85x6 : RowFact 7 85 ⟨true,true,false⟩ :=
  checked_row (mask:=0x60000001900000020800000408000002080000020800000150000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x85 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x85x7 : RowFact 7 85 ⟨true,true,true⟩ :=
  checked_row (mask:=0x40000001a00000021000000208000004080000020800000108000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x85 (by decide +kernel) (by decide +kernel)

theorem checked7x85 (g : Orientation) : RowFact 7 85 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x85x0
  · exact part7x85x1
  · exact part7x85x2
  · exact part7x85x3
  · exact part7x85x4
  · exact part7x85x5
  · exact part7x85x6
  · exact part7x85x7

private def cache7x86 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x60000000f00000001)
  | ⟨false,false,true⟩ => (-63,0x8000000780000003)
  | ⟨false,true,false⟩ => (0,0xc0000001e0000001)
  | ⟨false,true,true⟩ => (-66,0x40000000780000003)
  | ⟨true,false,false⟩ => (0,0x2000000060000000600000003)
  | ⟨true,false,true⟩ => (-95,0x1800000030000000300000001)
  | ⟨true,true,false⟩ => (-1,0x1000000018000000180000003)
  | ⟨true,true,true⟩ => (-97,0x3000000018000000180000001)

set_option maxRecDepth 20000 in
private theorem view7x86 (g : Orientation) : cache7x86 g=views (shape 7 86) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x86x0 : RowFact 7 86 ⟨false,false,false⟩ :=
  checked_row (mask:=0x600000009c000001020000010100000081000000720000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x86 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x86x1 : RowFact 7 86 ⟨false,false,true⟩ :=
  checked_row (mask:=0x3800000044000000820000010100000101000000ee00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x86 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x86x2 : RowFact 7 86 ⟨false,true,false⟩ :=
  checked_row (mask:=0x6000000390000004080000080800000408000003900000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x86 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x86x3 : RowFact 7 86 ⟨false,true,true⟩ :=
  checked_row (mask:=0x1c000000220000004100000080800000708000000e800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x86 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x86x4 : RowFact 7 86 ⟨true,false,false⟩ :=
  checked_row (mask:=0x7000000088000001040000008200000082000000820000007400000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x86 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x86x5 : RowFact 7 86 ⟨true,false,true⟩ :=
  checked_row (mask:=0x300000004800000084000000820000008200000102000000e400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x86 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x86x6 : RowFact 7 86 ⟨true,true,false⟩ :=
  checked_row (mask:=0xe00000011000000208000004080000041000000210000001d000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x86 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x86x7 : RowFact 7 86 ⟨true,true,true⟩ :=
  checked_row (mask:=0xc00000012000000210000004100000041000000208000001c800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x86 (by decide +kernel) (by decide +kernel)

theorem checked7x86 (g : Orientation) : RowFact 7 86 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x86x0
  · exact part7x86x1
  · exact part7x86x2
  · exact part7x86x3
  · exact part7x86x4
  · exact part7x86x5
  · exact part7x86x6
  · exact part7x86x7

private def cache7x87 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0x20000000f00000009)
  | ⟨false,false,true⟩ => (-63,0x48000000780000001)
  | ⟨false,true,false⟩ => (-3,0x40000000f00000009)
  | ⟨false,true,true⟩ => (-65,0x240000003c0000001)
  | ⟨true,false,false⟩ => (0,0x3000000020000000600000003)
  | ⟨true,false,true⟩ => (-96,0x3000000060000000200000003)
  | ⟨true,true,false⟩ => (-1,0x3000000010000000180000003)
  | ⟨true,true,true⟩ => (-97,0x3000000018000000100000003)

set_option maxRecDepth 20000 in
private theorem view7x87 (g : Orientation) : cache7x87 g=views (shape 7 87) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x87x0 : RowFact 7 87 ⟨false,false,false⟩ :=
  checked_row (mask:=0x24000000da000001010000010100000101000000b60000004800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x87 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x87x1 : RowFact 7 87 ⟨false,false,true⟩ :=
  checked_row (mask:=0x100000006c0000008200000101000001010000016d00000092000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x87 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x87x2 : RowFact 7 87 ⟨false,true,false⟩ :=
  checked_row (mask:=0x120000006d0000008080000080800000808000006d00000012000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x87 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x87x3 : RowFact 7 87 ⟨false,true,true⟩ :=
  checked_row (mask:=0x40000001a000000610000008080000080800000b6800000490000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x87 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x87x4 : RowFact 7 87 ⟨true,false,false⟩ :=
  checked_row (mask:=0x30000000c80000010400000102000000820000010400000124000000d8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x87 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x87x5 : RowFact 7 87 ⟨true,false,true⟩ :=
  checked_row (mask:=0x30000000c80000010400000104000000820000010200000124000000d8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x87 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x87x6 : RowFact 7 87 ⟨true,true,false⟩ :=
  checked_row (mask:=0x60000001900000020800000408000004100000020800000248000001b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x87 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x87x7 : RowFact 7 87 ⟨true,true,true⟩ :=
  checked_row (mask:=0x60000001900000020800000208000004100000040800000248000001b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x87 (by decide +kernel) (by decide +kernel)

theorem checked7x87 (g : Orientation) : RowFact 7 87 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x87x0
  · exact part7x87x1
  · exact part7x87x2
  · exact part7x87x3
  · exact part7x87x4
  · exact part7x87x5
  · exact part7x87x6
  · exact part7x87x7

private def cache7x88 : Orientation → ℤ × ℕ
  | ⟨false,false,false⟩ => (0,0xa0000000f00000001)
  | ⟨false,false,true⟩ => (-63,0x8000000780000005)
  | ⟨false,true,false⟩ => (0,0xa0000001e0000001)
  | ⟨false,true,true⟩ => (-67,0x80000000f00000005)
  | ⟨true,false,false⟩ => (0,0x6000000020000000600000003)
  | ⟨true,false,true⟩ => (-95,0x1800000030000000100000003)
  | ⟨true,true,false⟩ => (-1,0x1800000010000000180000003)
  | ⟨true,true,true⟩ => (-98,0x6000000030000000200000003)

set_option maxRecDepth 20000 in
private theorem view7x88 (g : Orientation) : cache7x88 g=views (shape 7 88) g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c <;> decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x88x0 : RowFact 7 88 ⟨false,false,false⟩ :=
  checked_row (mask:=0xa00000015c000001020000010100000081000000750000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x88 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x88x1 : RowFact 7 88 ⟨false,false,true⟩ :=
  checked_row (mask:=0x54000000aa000001010000010100000101000000ee00000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x88 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x88x2 : RowFact 7 88 ⟨false,true,false⟩ :=
  checked_row (mask:=0xa00000075000000808000008080000080800000750000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x88 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x88x3 : RowFact 7 88 ⟨false,true,true⟩ :=
  checked_row (mask:=0x54000000aa0000008100000080800000708000000e800000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x88 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x88x4 : RowFact 7 88 ⟨true,false,false⟩ :=
  checked_row (mask:=0xf00000010800000104000000820000008200000082000000720000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x88 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x88x5 : RowFact 7 88 ⟨true,false,true⟩ :=
  checked_row (mask:=0x780000008400000082000000820000010200000102000000e400000018000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x88 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x88x6 : RowFact 7 88 ⟨true,true,false⟩ :=
  checked_row (mask:=0x1e000000210000004080000040800000410000004100000039000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x88 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 2400000 in
private theorem part7x88x7 : RowFact 7 88 ⟨true,true,true⟩ :=
  checked_row (mask:=0x3c00000042000000410000004100000041000000208000001c800000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) view7x88 (by decide +kernel) (by decide +kernel)

theorem checked7x88 (g : Orientation) : RowFact 7 88 g := by
  obtain ⟨a,b,c⟩:=g
  cases a <;> cases b <;> cases c
  · exact part7x88x0
  · exact part7x88x1
  · exact part7x88x2
  · exact part7x88x3
  · exact part7x88x4
  · exact part7x88x5
  · exact part7x88x6
  · exact part7x88x7

end HalfIndexRows
