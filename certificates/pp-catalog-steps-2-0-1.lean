import certificates.«pp-catalog-core»

open OMA.S_oeis_a380455 PrimePolyFactor

namespace HalfCatalogue

private def rows2x0 : List Assignment := [
⟨{(-1,0),(0,0),(0,1)},1,⟨false,true,false⟩,(0,0)⟩,
⟨{(-1,1),(0,0),(0,1)},1,⟨false,true,true⟩,(0,1)⟩,
⟨{(0,-1),(0,0),(0,1)},0,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2)},0,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,0)},1,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1)},1,⟨false,false,true⟩,(0,1)⟩]

set_option maxRecDepth 20000 in
theorem step2x0 : extensionComplete 2 0 :=
  transition_of_check (rows:=rows2x0) (by decide +kernel)

end HalfCatalogue
