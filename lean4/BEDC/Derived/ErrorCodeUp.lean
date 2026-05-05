import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.ErrorCodeUp

open BEDC.FKernel.Hist
open BEDC.Derived.VecSpaceUp

def ErrorCodeSingletonCodeword (h : BHist) : Prop :=
  VecSpaceSingletonCarrier h ∧ VecSpaceSingletonClassifier h BHist.Empty

def ErrorCodeSingletonWithinRadius (c r t : BHist) : Prop :=
  VecSpaceSingletonClassifier c BHist.Empty ∧ hsame r t ∧ VecSpaceSingletonCarrier t

theorem ErrorCodeSingleton_unique_decoding_radius {c1 c2 r t : BHist} :
    ErrorCodeSingletonCodeword c1 ->
      ErrorCodeSingletonCodeword c2 ->
        ErrorCodeSingletonWithinRadius c1 r t ->
          ErrorCodeSingletonWithinRadius c2 r t ->
            hsame t BHist.Empty -> VecSpaceSingletonClassifier c1 c2 := by
  intro codewordLeft codewordRight radiusLeft radiusRight targetEmpty
  have receivedEmpty : hsame r BHist.Empty :=
    hsame_trans radiusLeft.right.left targetEmpty
  have radiusRightEndpoint : hsame r BHist.Empty :=
    hsame_trans radiusRight.right.left radiusRight.right.right
  have leftEmpty : hsame c1 BHist.Empty :=
    hsame_trans codewordLeft.left radiusLeft.left.right.left
  have rightEmpty : hsame c2 BHist.Empty :=
    hsame_trans codewordRight.left radiusRight.left.right.left
  have sameCodewords : hsame c1 c2 :=
    hsame_trans leftEmpty
      (hsame_trans (hsame_symm receivedEmpty)
        (hsame_trans radiusRightEndpoint (hsame_symm rightEmpty)))
  exact And.intro leftEmpty (And.intro rightEmpty sameCodewords)

end BEDC.Derived.ErrorCodeUp
