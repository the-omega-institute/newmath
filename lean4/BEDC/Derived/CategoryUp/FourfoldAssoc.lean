import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CategoryHomCarrier_fourfold_assoc_witness
    {a b c d e f g h i fg fgh hi ghi left right : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> CategoryHomCarrier c d h ->
      CategoryHomCarrier d e i -> Cont f g fg -> Cont fg h fgh -> Cont h i hi ->
        Cont g hi ghi -> Cont fgh i left -> Cont f ghi right ->
          CategoryHomCarrier a e left ∧ CategoryHomCarrier a e right ∧ hsame left right := by
  intro first second third fourth fgRel fghRel hiRel ghiRel leftRel rightRel
  have fgCarrier : CategoryHomCarrier a c fg :=
    CategoryHomCarrier_comp_closed first second fgRel
  have fghCarrier : CategoryHomCarrier a d fgh :=
    CategoryHomCarrier_comp_closed fgCarrier third fghRel
  have hiCarrier : CategoryHomCarrier c e hi :=
    CategoryHomCarrier_comp_closed third fourth hiRel
  have ghiCarrier : CategoryHomCarrier b e ghi :=
    CategoryHomCarrier_comp_closed second hiCarrier ghiRel
  exact
    And.intro (CategoryHomCarrier_comp_closed fghCarrier fourth leftRel)
      (And.intro (CategoryHomCarrier_comp_closed first ghiCarrier rightRel)
        (cont_assoc_four fgRel fghRel hiRel ghiRel leftRel rightRel))

end BEDC.Derived.CategoryUp
