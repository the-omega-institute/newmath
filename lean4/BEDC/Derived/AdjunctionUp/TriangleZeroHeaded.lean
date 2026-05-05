import BEDC.Derived.AdjunctionUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatTransUp

theorem AdjunctionTriangleCarrier_zero_headed_component_absurd
    {left right object unit counit leftLeg rightLeg : BHist} :
    AdjunctionTriangleCarrier left right object unit counit leftLeg rightLeg ->
      ((∃ z : BHist, left = BHist.e0 z) ∨ (∃ z : BHist, right = BHist.e0 z) ∨
        (∃ z : BHist, object = BHist.e0 z) ∨ (∃ z : BHist, unit = BHist.e0 z) ∨
          (∃ z : BHist, counit = BHist.e0 z) ∨
            (∃ z : BHist, leftLeg = BHist.e0 z) ∨
              (∃ z : BHist, rightLeg = BHist.e0 z)) -> False := by
  intro carrier zeroComponent
  cases zeroComponent with
  | inl leftZero =>
      exact NatTransPrefixComponentCarrier_zero_headed_component_absurd carrier.left
        (Or.inl leftZero)
  | inr rest =>
      cases rest with
      | inl rightZero =>
          exact NatTransPrefixComponentCarrier_zero_headed_component_absurd carrier.left
            (Or.inr (Or.inl rightZero))
      | inr rest =>
          cases rest with
          | inl objectZero =>
              exact NatTransPrefixComponentCarrier_zero_headed_component_absurd carrier.left
                (Or.inr (Or.inr (Or.inl objectZero)))
          | inr rest =>
              cases rest with
              | inl unitZero =>
                  exact NatTransPrefixComponentCarrier_zero_headed_component_absurd carrier.left
                    (Or.inr (Or.inr (Or.inr unitZero)))
              | inr rest =>
                  cases rest with
                  | inl counitZero =>
                      exact NatTransPrefixComponentCarrier_zero_headed_component_absurd
                        carrier.right.left (Or.inr (Or.inr (Or.inr counitZero)))
                  | inr rest =>
                      have unitUnary : UnaryHistory unit :=
                        carrier.left.right.right.right.right.right.left
                      have counitUnary : UnaryHistory counit :=
                        carrier.right.left.right.right.right.right.right.left
                      cases rest with
                      | inl leftLegZero =>
                          have leftLegUnary : UnaryHistory leftLeg :=
                            unary_cont_closed unitUnary counitUnary carrier.right.right.left
                          cases leftLegZero with
                          | intro z leftLegEq =>
                              cases leftLegEq
                              exact unary_no_zero_extension leftLegUnary
                      | inr rightLegZero =>
                          have rightLegUnary : UnaryHistory rightLeg :=
                            unary_cont_closed counitUnary unitUnary carrier.right.right.right
                          cases rightLegZero with
                          | intro z rightLegEq =>
                              cases rightLegEq
                              exact unary_no_zero_extension rightLegUnary

end BEDC.Derived.AdjunctionUp
