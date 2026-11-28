import certificates.«pp-catalog-core»

open OMA.S_oeis_a380455 PrimePolyFactor

namespace HalfCatalogue

private def rows3x0 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2)},1,⟨false,true,false⟩,(0,0)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2)},2,⟨false,true,false⟩,(0,0)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2)},1,⟨false,true,true⟩,(0,2)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2)},0,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(0,3)},0,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0)},1,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,1)},2,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,2)},1,⟨false,false,true⟩,(0,2)⟩]

set_option maxRecDepth 20000 in
theorem step3x0 : extensionComplete 3 0 :=
  transition_of_check (rows:=rows3x0) (by decide +kernel)

private def rows3x1 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(1,0)},2,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(1,0)},4,⟨true,false,true⟩,(0,1)⟩,
⟨{(0,-1),(0,0),(0,1),(1,0)},2,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(1,0)},1,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,-1),(1,0)},4,⟨false,false,true⟩,(0,1)⟩,
⟨{(0,0),(0,1),(1,0),(1,1)},3,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,0),(2,0)},1,⟨true,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step3x1 : extensionComplete 3 1 :=
  transition_of_check (rows:=rows3x1) (by decide +kernel)

end HalfCatalogue
