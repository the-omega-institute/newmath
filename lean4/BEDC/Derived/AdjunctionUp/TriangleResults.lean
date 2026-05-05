import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.NatTransUp

theorem AdjunctionUnitCounitTriangle_results_hsame
    {p q a unit counit left right : BHist} :
    NatTransPrefixComponentCarrier p q a unit ->
      NatTransPrefixComponentCarrier q p a counit ->
        Cont unit counit left -> Cont counit unit right -> hsame left right := by
  intro unitCarrier counitCarrier leftRel rightRel
  have leftEmpty :=
    AdjunctionPrefix_unit_counit_composite_empty unitCarrier counitCarrier leftRel
  have rightEmpty :=
    AdjunctionPrefix_unit_counit_composite_empty counitCarrier unitCarrier rightRel
  exact hsame_trans leftEmpty.right (hsame_symm rightEmpty.right)

end BEDC.Derived.AdjunctionUp
