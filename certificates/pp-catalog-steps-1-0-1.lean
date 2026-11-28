import certificates.«pp-catalog-core»

open OMA.S_oeis_a380455 PrimePolyFactor

namespace HalfCatalogue

private def rows1x0 : List Assignment := [
⟨{(-1,0),(0,0)},0,⟨true,false,false⟩,(0,1)⟩,
⟨{(0,-1),(0,0)},0,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1)},0,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(1,0)},0,⟨true,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step1x0 : extensionComplete 1 0 :=
  transition_of_check (rows:=rows1x0) (by decide +kernel)

end HalfCatalogue
