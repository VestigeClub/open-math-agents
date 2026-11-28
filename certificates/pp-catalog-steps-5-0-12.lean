import certificates.«pp-catalog-core»

open OMA.S_oeis_a380455 PrimePolyFactor

namespace HalfCatalogue

private def rows5x0 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2),(0,3),(0,4)},1,⟨false,true,false⟩,(0,0)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2),(0,3),(0,4)},2,⟨false,true,false⟩,(0,0)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2),(0,3),(0,4)},3,⟨false,true,false⟩,(0,0)⟩,
⟨{(-1,3),(0,0),(0,1),(0,2),(0,3),(0,4)},2,⟨false,true,true⟩,(0,4)⟩,
⟨{(-1,4),(0,0),(0,1),(0,2),(0,3),(0,4)},1,⟨false,true,true⟩,(0,4)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2),(0,3),(0,4)},0,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(0,4),(0,5)},0,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(0,4),(1,0)},1,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(0,4),(1,1)},2,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(0,4),(1,2)},3,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(0,4),(1,3)},2,⟨false,false,true⟩,(0,4)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(0,4),(1,4)},1,⟨false,false,true⟩,(0,4)⟩]

set_option maxRecDepth 20000 in
theorem step5x0 : extensionComplete 5 0 :=
  transition_of_check (rows:=rows5x0) (by decide +kernel)

private def rows5x1 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2),(0,3),(1,0)},18,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2),(0,3),(1,0)},29,⟨true,false,true⟩,(0,1)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2),(0,3),(1,0)},31,⟨true,false,true⟩,(0,1)⟩,
⟨{(-1,3),(0,0),(0,1),(0,2),(0,3),(1,0)},32,⟨true,false,true⟩,(0,1)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2),(0,3),(1,0)},2,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(0,4),(1,0)},1,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,-1),(1,0)},10,⟨false,false,true⟩,(0,3)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,0),(1,1)},4,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,0),(1,2)},5,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,0),(1,3)},6,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,0),(2,0)},7,⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step5x1 : extensionComplete 5 1 :=
  transition_of_check (rows:=rows5x1) (by decide +kernel)

private def rows5x2 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2),(0,3),(1,1)},29,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2),(0,3),(1,1)},33,⟨false,false,false⟩,(1,0)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2),(0,3),(1,1)},34,⟨false,false,true⟩,(1,3)⟩,
⟨{(-1,3),(0,0),(0,1),(0,2),(0,3),(1,1)},31,⟨true,true,false⟩,(3,1)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2),(0,3),(1,1)},3,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(0,4),(1,1)},2,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,0),(1,1)},4,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,1),(1,2)},8,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,1),(1,3)},5,⟨false,false,true⟩,(0,3)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,1),(2,1)},9,⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step5x2 : extensionComplete 5 2 :=
  transition_of_check (rows:=rows5x2) (by decide +kernel)

private def rows5x3 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2),(1,0),(1,1)},13,⟨true,false,true⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2),(1,0),(1,1)},23,⟨false,true,false⟩,(1,0)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2),(1,0),(1,1)},24,⟨false,true,false⟩,(1,0)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2),(1,0),(1,1)},8,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,0),(1,1)},4,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,-1),(1,0),(1,1)},16,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,1),(1,2)},11,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,1),(2,0)},12,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,1),(2,1)},13,⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step5x3 : extensionComplete 5 3 :=
  transition_of_check (rows:=rows5x3) (by decide +kernel)

private def rows5x4 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2),(1,0),(1,2)},17,⟨true,false,true⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2),(1,0),(1,2)},28,⟨true,false,true⟩,(0,1)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2),(1,0),(1,2)},17,⟨true,true,true⟩,(2,1)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2),(1,0),(1,2)},5,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,0),(1,2)},5,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,-1),(1,0),(1,2)},14,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,1),(1,2)},11,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,2),(1,3)},14,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,2),(2,0)},15,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,2),(2,2)},15,⟨false,false,true⟩,(0,2)⟩]

set_option maxRecDepth 20000 in
theorem step5x4 : extensionComplete 5 4 :=
  transition_of_check (rows:=rows5x4) (by decide +kernel)

private def rows5x5 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2),(1,0),(2,0)},9,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2),(1,0),(2,0)},20,⟨true,false,true⟩,(0,2)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2),(1,0),(2,0)},22,⟨true,false,true⟩,(0,2)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2),(1,0),(2,0)},9,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,0),(2,0)},7,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,-1),(1,0),(2,0)},20,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,1),(2,0)},12,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,2),(2,0)},15,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(2,-1),(2,0)},22,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(2,0),(2,1)},15,⟨true,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(2,0),(3,0)},7,⟨true,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step5x5 : extensionComplete 5 5 :=
  transition_of_check (rows:=rows5x5) (by decide +kernel)

private def rows5x6 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2),(1,1),(2,1)},25,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2),(1,1),(2,1)},33,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2),(1,1),(2,1)},25,⟨true,true,false⟩,(2,1)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2),(1,1),(2,1)},9,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,1),(2,1)},9,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,1),(2,1)},13,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(1,2),(2,1)},13,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(2,0),(2,1)},17,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(2,1),(2,2)},17,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(2,1),(3,1)},18,⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step5x6 : extensionComplete 5 6 :=
  transition_of_check (rows:=rows5x6) (by decide +kernel)

private def rows5x7 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(0,2),(1,2),(1,3)},27,⟨false,true,true⟩,(1,3)⟩,
⟨{(-1,1),(0,0),(0,1),(0,2),(1,2),(1,3)},26,⟨false,true,true⟩,(1,3)⟩,
⟨{(-1,2),(0,0),(0,1),(0,2),(1,2),(1,3)},25,⟨false,true,true⟩,(1,3)⟩,
⟨{(0,-1),(0,0),(0,1),(0,2),(1,2),(1,3)},10,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(0,3),(1,2),(1,3)},4,⟨false,false,true⟩,(0,3)⟩,
⟨{(0,0),(0,1),(0,2),(1,0),(1,2),(1,3)},14,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(1,2),(1,3)},16,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,2),(1,3),(1,4)},19,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,2),(1,3),(2,2)},20,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(0,2),(1,2),(1,3),(2,3)},21,⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step5x7 : extensionComplete 5 7 :=
  transition_of_check (rows:=rows5x7) (by decide +kernel)

private def rows5x8 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(1,1),(1,2),(2,1)},26,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(1,1),(1,2),(2,1)},34,⟨true,false,false⟩,(0,1)⟩,
⟨{(0,-1),(0,0),(0,1),(1,1),(1,2),(2,1)},20,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(1,2),(2,1)},13,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(1,0),(1,1),(1,2),(2,1)},23,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(1,3),(2,1)},25,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(2,0),(2,1)},28,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(2,1),(2,2)},24,⟨true,true,true⟩,(2,2)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(2,1),(3,1)},29,⟨false,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step5x8 : extensionComplete 5 8 :=
  transition_of_check (rows:=rows5x8) (by decide +kernel)

private def rows5x9 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(1,1),(1,2),(2,2)},30,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(1,1),(1,2),(2,2)},26,⟨true,true,true⟩,(2,2)⟩,
⟨{(0,-1),(0,0),(0,1),(1,1),(1,2),(2,2)},21,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)},12,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(1,0),(1,1),(1,2),(2,2)},24,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(1,3),(2,2)},26,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(2,1),(2,2)},24,⟨true,true,true⟩,(2,2)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(2,2),(2,3)},30,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(2,2),(3,2)},21,⟨true,true,true⟩,(2,3)⟩]

set_option maxRecDepth 20000 in
theorem step5x9 : extensionComplete 5 9 :=
  transition_of_check (rows:=rows5x9) (by decide +kernel)

private def rows5x10 : List Assignment := [
⟨{(-1,0),(0,0),(0,1),(1,1),(2,1),(2,2)},27,⟨true,false,false⟩,(0,1)⟩,
⟨{(-1,1),(0,0),(0,1),(1,1),(2,1),(2,2)},31,⟨false,true,true⟩,(2,2)⟩,
⟨{(0,-1),(0,0),(0,1),(1,1),(2,1),(2,2)},22,⟨false,false,false⟩,(0,1)⟩,
⟨{(0,0),(0,1),(0,2),(1,1),(2,1),(2,2)},17,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(1,0),(1,1),(2,1),(2,2)},24,⟨true,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(1,2),(2,1),(2,2)},24,⟨true,true,true⟩,(2,2)⟩,
⟨{(0,0),(0,1),(1,1),(2,0),(2,1),(2,2)},17,⟨false,true,false⟩,(2,0)⟩,
⟨{(0,0),(0,1),(1,1),(2,1),(2,2),(2,3)},22,⟨false,true,true⟩,(2,3)⟩,
⟨{(0,0),(0,1),(1,1),(2,1),(2,2),(3,1)},31,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,0),(0,1),(1,1),(2,1),(2,2),(3,2)},27,⟨true,true,true⟩,(2,3)⟩]

set_option maxRecDepth 20000 in
theorem step5x10 : extensionComplete 5 10 :=
  transition_of_check (rows:=rows5x10) (by decide +kernel)

private def rows5x11 : List Assignment := [
⟨{(-1,1),(0,1),(1,0),(1,1),(1,2),(2,1)},33,⟨true,false,true⟩,(0,2)⟩,
⟨{(0,0),(0,1),(1,0),(1,1),(1,2),(2,1)},23,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,1),(0,2),(1,0),(1,1),(1,2),(2,1)},23,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,1),(1,-1),(1,0),(1,1),(1,2),(2,1)},33,⟨false,false,true⟩,(0,2)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(1,3),(2,1)},33,⟨false,false,false⟩,(0,0)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(2,0),(2,1)},23,⟨false,true,false⟩,(2,0)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(2,1),(2,2)},23,⟨false,true,true⟩,(2,2)⟩,
⟨{(0,1),(1,0),(1,1),(1,2),(2,1),(3,1)},33,⟨true,false,false⟩,(0,0)⟩]

set_option maxRecDepth 20000 in
theorem step5x11 : extensionComplete 5 11 :=
  transition_of_check (rows:=rows5x11) (by decide +kernel)

end HalfCatalogue
