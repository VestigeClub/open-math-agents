import certificates.«pp-catalog-core»

open OMA.S_oeis_a380455 PrimePolyFactor

namespace HalfCatalogue

private def rows4x0 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2),(0,3)},1,⟨false,true,false⟩,(0,0)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2),(0,3)},2,⟨false,true,false⟩,(0,0)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2),(0,3)},2,⟨false,true,true⟩,(0,3)⟩,
⟨{(-1,3),(0,0),(0,1),(0,2),(0,3)},1,⟨false,true,true⟩,(0,3)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2),(0,3)},0,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(0,4)},0,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,0)},1,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,1)},2,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,2)},2,⟨false,false,true⟩,(0,3)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,3)},1,⟨false,false,true⟩,(0,3)⟩]

set_option maxRecDepth 20000 in
theorem step4x0 : extensionComplete 4 0 :=
  transition_of_check (rows:=rows4x0) (by decide +kernel)

private def rows4x1 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2),(1,0)},6,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2),(1,0)},8,⟨true,false,true⟩,(0,1)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2),(1,0)},10,⟨true,false,true⟩,(0,1)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2),(1,0)},2,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,0)},1,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,-1),(1,0)},7,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,1)},3,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,2)},4,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(2,0)},5,⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step4x1 : extensionComplete 4 1 :=
  transition_of_check (rows:=rows4x1) (by decide +kernel)

private def rows4x2 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2),(1,1)},8,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2),(1,1)},11,⟨false,false,false⟩,(1,0)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2),(1,1)},8,⟨true,true,false⟩,(2,1)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2),(1,1)},2,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,1)},2,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,1)},3,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(1,2)},3,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(2,1)},6,⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step4x2 : extensionComplete 4 2 :=
  transition_of_check (rows:=rows4x2) (by decide +kernel)

private def rows4x3 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(1,0),(1,1)},3,⟨true,false,true⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(1,0),(1,1)},3,⟨true,true,true⟩,(1,1)⟩,
⟨{(0,-1),(0,0),(0,1),(1,0),(1,1)},3,⟨false,false,true⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,1)},3,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,-1),(1,0),(1,1)},3,⟨false,true,true⟩,(1,1)⟩,
⟨{(0,0),(0,1),(1,0),(1,1),(1,2)},3,⟨false,true,false⟩,(1,0)⟩,
⟨{(0,0),(0,1),(1,0),(1,1),(2,0)},3,⟨true,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,0),(1,1),(2,1)},3,⟨true,true,false⟩,(1,0)⟩]

set_option maxRecDepth 20000 in
theorem step4x3 : extensionComplete 4 3 :=
  transition_of_check (rows:=rows4x3) (by decide +kernel)

private def rows4x4 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(1,1),(1,2)},9,⟨false,true,true⟩,(1,2)⟩,
⟨{(-1,1),(0,0),(0,1),(1,1),(1,2)},8,⟨false,true,true⟩,(1,2)⟩,
⟨{(0,-1),(0,0),(0,1),(1,1),(1,2)},7,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(1,2)},3,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(1,0),(1,1),(1,2)},3,⟨false,true,false⟩,(1,0)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(1,3)},7,⟨false,true,true⟩,(1,3)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(2,1)},8,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(2,2)},9,⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step4x4 : extensionComplete 4 4 :=
  transition_of_check (rows:=rows4x4) (by decide +kernel)

end HalfCatalogue
