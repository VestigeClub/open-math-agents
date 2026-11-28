import certificates.«pp-catalog-steps-1-0-1»
import certificates.«pp-catalog-steps-2-0-1»
import certificates.«pp-catalog-steps-3-0-2»
import certificates.«pp-catalog-steps-4-0-5»
import certificates.«pp-catalog-steps-5-0-12»
import certificates.«pp-catalog-steps-6-0-16»
import certificates.«pp-catalog-steps-6-16-32»
import certificates.«pp-catalog-steps-6-32-35»
import certificates.«pp-catalog-steps-7-0-16»
import certificates.«pp-catalog-steps-7-16-32»
import certificates.«pp-catalog-steps-7-32-48»
import certificates.«pp-catalog-steps-7-48-64»
import certificates.«pp-catalog-steps-7-64-80»
import certificates.«pp-catalog-steps-7-80-96»
import certificates.«pp-catalog-steps-7-96-108»
import certificates.«pp-catalog-measures»

open OMA.S_oeis_a380455 PrimePolyFactor

namespace HalfCatalogue

theorem all_growth : completeGrowth := by
  intro area positive bound id valid
  interval_cases area

  · have h : id < 1 := by simpa only [count] using valid
    interval_cases id
    · exact step1x0

  · have h : id < 1 := by simpa only [count] using valid
    interval_cases id
    · exact step2x0

  · have h : id < 2 := by simpa only [count] using valid
    interval_cases id
    · exact step3x0
    · exact step3x1

  · have h : id < 5 := by simpa only [count] using valid
    interval_cases id
    · exact step4x0
    · exact step4x1
    · exact step4x2
    · exact step4x3
    · exact step4x4

  · have h : id < 12 := by simpa only [count] using valid
    interval_cases id
    · exact step5x0
    · exact step5x1
    · exact step5x2
    · exact step5x3
    · exact step5x4
    · exact step5x5
    · exact step5x6
    · exact step5x7
    · exact step5x8
    · exact step5x9
    · exact step5x10
    · exact step5x11

  · have h : id < 35 := by simpa only [count] using valid
    interval_cases id
    · exact step6x0
    · exact step6x1
    · exact step6x2
    · exact step6x3
    · exact step6x4
    · exact step6x5
    · exact step6x6
    · exact step6x7
    · exact step6x8
    · exact step6x9
    · exact step6x10
    · exact step6x11
    · exact step6x12
    · exact step6x13
    · exact step6x14
    · exact step6x15
    · exact step6x16
    · exact step6x17
    · exact step6x18
    · exact step6x19
    · exact step6x20
    · exact step6x21
    · exact step6x22
    · exact step6x23
    · exact step6x24
    · exact step6x25
    · exact step6x26
    · exact step6x27
    · exact step6x28
    · exact step6x29
    · exact step6x30
    · exact step6x31
    · exact step6x32
    · exact step6x33
    · exact step6x34

  · have h : id < 108 := by simpa only [count] using valid
    interval_cases id
    · exact step7x0
    · exact step7x1
    · exact step7x2
    · exact step7x3
    · exact step7x4
    · exact step7x5
    · exact step7x6
    · exact step7x7
    · exact step7x8
    · exact step7x9
    · exact step7x10
    · exact step7x11
    · exact step7x12
    · exact step7x13
    · exact step7x14
    · exact step7x15
    · exact step7x16
    · exact step7x17
    · exact step7x18
    · exact step7x19
    · exact step7x20
    · exact step7x21
    · exact step7x22
    · exact step7x23
    · exact step7x24
    · exact step7x25
    · exact step7x26
    · exact step7x27
    · exact step7x28
    · exact step7x29
    · exact step7x30
    · exact step7x31
    · exact step7x32
    · exact step7x33
    · exact step7x34
    · exact step7x35
    · exact step7x36
    · exact step7x37
    · exact step7x38
    · exact step7x39
    · exact step7x40
    · exact step7x41
    · exact step7x42
    · exact step7x43
    · exact step7x44
    · exact step7x45
    · exact step7x46
    · exact step7x47
    · exact step7x48
    · exact step7x49
    · exact step7x50
    · exact step7x51
    · exact step7x52
    · exact step7x53
    · exact step7x54
    · exact step7x55
    · exact step7x56
    · exact step7x57
    · exact step7x58
    · exact step7x59
    · exact step7x60
    · exact step7x61
    · exact step7x62
    · exact step7x63
    · exact step7x64
    · exact step7x65
    · exact step7x66
    · exact step7x67
    · exact step7x68
    · exact step7x69
    · exact step7x70
    · exact step7x71
    · exact step7x72
    · exact step7x73
    · exact step7x74
    · exact step7x75
    · exact step7x76
    · exact step7x77
    · exact step7x78
    · exact step7x79
    · exact step7x80
    · exact step7x81
    · exact step7x82
    · exact step7x83
    · exact step7x84
    · exact step7x85
    · exact step7x86
    · exact step7x87
    · exact step7x88
    · exact step7x89
    · exact step7x90
    · exact step7x91
    · exact step7x92
    · exact step7x93
    · exact step7x94
    · exact step7x95
    · exact step7x96
    · exact step7x97
    · exact step7x98
    · exact step7x99
    · exact step7x100
    · exact step7x101
    · exact step7x102
    · exact step7x103
    · exact step7x104
    · exact step7x105
    · exact step7x106
    · exact step7x107

theorem representative {f : Shape} (poly : polyomino f) (area : ℕ)
    (positive : 0<area) (bound : area≤8) (size : f.card=area) :
    ∃ id < count area, congruent f (shapeCells area id).toFinset :=
  represented_of_growth all_growth poly area positive bound size

theorem representative_2 {f : Shape} (poly : polyomino f) (size : f.card=2) :
    ∃ id < 1, congruent f (shapeCells 2 id).toFinset :=
  representative poly 2 (by decide) (by decide) size

theorem representative_4 {f : Shape} (poly : polyomino f) (size : f.card=4) :
    ∃ id < 5, congruent f (shapeCells 4 id).toFinset :=
  representative poly 4 (by decide) (by decide) size

theorem representative_7 {f : Shape} (poly : polyomino f) (size : f.card=7) :
    ∃ id < 108, congruent f (shapeCells 7 id).toFinset :=
  representative poly 7 (by decide) (by decide) size

theorem representative_8 {f : Shape} (poly : polyomino f) (size : f.card=8) :
    ∃ id < 369, congruent f (shapeCells 8 id).toFinset :=
  representative poly 8 (by decide) (by decide) size

end HalfCatalogue
