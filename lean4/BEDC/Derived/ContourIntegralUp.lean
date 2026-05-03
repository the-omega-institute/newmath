import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ContourIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def PLContourSegment (gamma : BHist) : Prop :=
  ∃ z0 : BHist, ∃ z1 : BHist,
    ComplexHistoryCarrier z0 ∧ ComplexHistoryCarrier z1 ∧ Cont z0 z1 gamma

theorem PLContourSegment_unary_result {gamma : BHist} :
    PLContourSegment gamma ->
      ∃ z0 : BHist, ∃ z1 : BHist,
        ComplexHistoryCarrier z0 ∧ ComplexHistoryCarrier z1 ∧ Cont z0 z1 gamma ∧
          UnaryHistory gamma := by
  intro segment
  cases segment with
  | intro z0 rest =>
      cases rest with
      | intro z1 data =>
          cases data with
          | intro z0Carrier rest =>
              cases rest with
              | intro z1Carrier z0z1 =>
                  have z0Unary : UnaryHistory z0 := ComplexHistoryCarrier_unary z0Carrier
                  have z1Unary : UnaryHistory z1 := ComplexHistoryCarrier_unary z1Carrier
                  have gammaUnary : UnaryHistory gamma :=
                    unary_cont_closed z0Unary z1Unary z0z1
                  exact Exists.intro z0
                    (Exists.intro z1
                      (And.intro z0Carrier
                        (And.intro z1Carrier
                          (And.intro z0z1 gammaUnary))))

theorem PLContourSegment_hsame_transport {gamma gamma' : BHist} :
    PLContourSegment gamma -> hsame gamma gamma' ->
      PLContourSegment gamma' ∧ UnaryHistory gamma' := by
  intro segment sameGamma
  cases segment with
  | intro z0 rest =>
      cases rest with
      | intro z1 data =>
          cases data with
          | intro z0Carrier rest =>
              cases rest with
              | intro z1Carrier z0z1 =>
                  have z0z1' : Cont z0 z1 gamma' :=
                    cont_result_hsame_transport z0z1 sameGamma
                  have gammaUnary' : UnaryHistory gamma' :=
                    unary_cont_closed (ComplexHistoryCarrier_unary z0Carrier)
                      (ComplexHistoryCarrier_unary z1Carrier) z0z1'
                  exact And.intro
                    (Exists.intro z0
                      (Exists.intro z1
                        (And.intro z0Carrier
                          (And.intro z1Carrier z0z1'))))
                    gammaUnary'

end BEDC.Derived.ContourIntegralUp
