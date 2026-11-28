import certificates.«pp-catalog-models»
open OMA.S_oeis_a380455
namespace HalfCatalogue
set_option maxRecDepth 20000 in
private theorem sizes : ∀ area : Fin 9, ∀ id : Fin 369,
    id.val < count area.val → (shape area.val id.val).card=area.val := by decide +kernel

theorem shape_card (area id : ℕ) (bound : area≤8) (valid : id<count area) :
    (shape area id).card=area := by
  have cap : count area≤369 := by interval_cases area <;> decide
  exact sizes ⟨area,by omega⟩ ⟨id,by omega⟩ valid
end HalfCatalogue
