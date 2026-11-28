import certificates.«pp-catalog-core»

open OMA.S_oeis_a380455 PrimePolyFactor

namespace HalfCatalogue

private def rows6x32 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(1,1),(2,1),(3,1),(3,2)},78,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(1,1),(2,1),(3,1),(3,2)},98,⟨false,true,true⟩,(3,2)⟩,
⟨{(0,-1),(0,0),(0,1),(1,1),(2,1),(3,1),(3,2)},66,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(2,1),(3,1),(3,2)},53,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(1,0),(1,1),(2,1),(3,1),(3,2)},72,⟨true,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(2,1),(3,1),(3,2)},88,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(2,0),(2,1),(3,1),(3,2)},88,⟨false,true,true⟩,(3,2)⟩,
⟨{(0,0),(0,1),(1,1),(2,1),(2,2),(3,1),(3,2)},72,⟨true,true,true⟩,(2,3)⟩,
⟨{(0,0),(0,1),(1,1),(2,1),(3,0),(3,1),(3,2)},53,⟨false,true,false⟩,(3,0)⟩,
⟨{(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(3,3)},66,⟨false,true,true⟩,(3,3)⟩,
⟨{(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,1)},98,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(2,1),(3,1),(3,2),(4,2)},78,⟨true,true,true⟩,(2,4)⟩]

set_option maxRecDepth 20000 in
theorem step6x32 : extensionComplete 6 32 :=
  transition_of_check (rows:=rows6x32) (by decide +kernel)

private def rows6x33 : List Assignment := [
⟨{(-1,1),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1)},104,⟨false,true,false⟩,(2,0)⟩,
⟨{(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,1)},70,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,1)},100,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,1)},93,⟨true,true,false⟩,(3,0)⟩,
⟨{(0,1),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,1)},107,⟨true,false,false⟩,(1,0)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,1)},101,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1)},70,⟨false,true,false⟩,(2,0)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)},100,⟨false,true,false⟩,(2,0)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,3)},93,⟨true,true,true⟩,(3,2)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(3,1)},104,⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step6x33 : extensionComplete 6 33 :=
  transition_of_check (rows:=rows6x33) (by decide +kernel)

private def rows6x34 : List Assignment := [
⟨{(-1,1),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2)},105,⟨false,true,true⟩,(2,3)⟩,
⟨{(0,0),(0,1),(1,0),(1,1),(1,2),(1,3),(2,2)},71,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,1),(0,2),(1,0),(1,1),(1,2),(1,3),(2,2)},100,⟨false,false,true⟩,(0,3)⟩,
⟨{(0,1),(0,3),(1,0),(1,1),(1,2),(1,3),(2,2)},85,⟨true,true,false⟩,(3,0)⟩,
⟨{(0,1),(1,-1),(1,0),(1,1),(1,2),(1,3),(2,2)},102,⟨false,true,true⟩,(2,3)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(1,3),(1,4),(2,2)},102,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(1,3),(2,0),(2,2)},85,⟨true,false,true⟩,(0,2)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(1,3),(2,1),(2,2)},100,⟨false,true,false⟩,(2,0)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(2,3)},71,⟨false,true,true⟩,(2,3)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(1,3),(2,2),(3,2)},105,⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step6x34 : extensionComplete 6 34 :=
  transition_of_check (rows:=rows6x34) (by decide +kernel)

end HalfCatalogue
