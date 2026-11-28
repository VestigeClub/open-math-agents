import certificates.«pp-catalog-models»

open OMA.S_oeis_a380455
namespace HalfPrimes

def exceptionCells : List Cell := [(-2,0),(-2,1),(-2,2),(-1,-1),(-1,0),(-1,1),(-1,2),(-1,3),(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3)]
def exceptionShape : Shape := exceptionCells.toFinset

theorem exception_area : exceptionShape.card=16 := by decide +kernel

end HalfPrimes
