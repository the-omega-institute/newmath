import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ExpMapUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ExpMapFlowLedger (source target flow endpoint : BHist) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ Cont source flow endpoint ∧ hsame endpoint target

theorem ExpMapFlowLedger_zero_and_composition_surface
    {source middle target flowLeft flowRight flowWhole leftEndpoint rightEndpoint
      wholeEndpoint : BHist} :
    ExpMapFlowLedger BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
      (ExpMapFlowLedger source middle flowLeft leftEndpoint ->
        hsame leftEndpoint middle ->
          ExpMapFlowLedger middle target flowRight rightEndpoint ->
            Cont flowLeft flowRight flowWhole ->
              Cont source flowWhole wholeEndpoint ->
                ExpMapFlowLedger source target flowWhole wholeEndpoint ∧
                  hsame target wholeEndpoint) := by
  have zeroLedger : ExpMapFlowLedger BHist.Empty BHist.Empty BHist.Empty BHist.Empty :=
    And.intro unary_empty
      (And.intro unary_empty
        (And.intro (cont_left_unit BHist.Empty) (hsame_refl BHist.Empty)))
  constructor
  · exact zeroLedger
  · intro leftLedger sameLeftMiddle rightLedger flowComposite sourceComposite
    have sameComposedEndpoint : hsame rightEndpoint wholeEndpoint :=
      by
        cases sameLeftMiddle
        exact cont_assoc_relational leftLedger.right.right.left rightLedger.right.right.left
          flowComposite sourceComposite
    have targetWhole : hsame target wholeEndpoint :=
      hsame_trans (hsame_symm rightLedger.right.right.right) sameComposedEndpoint
    exact And.intro
      (And.intro leftLedger.left
        (And.intro rightLedger.right.left
          (And.intro sourceComposite (hsame_symm targetWhole))))
      targetWhole

end BEDC.Derived.ExpMapUp
