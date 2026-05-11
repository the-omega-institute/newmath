import BEDC.Derived.CurvatureUp

namespace BEDC.Derived.CurvatureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CurvatureBracketCarrier_classifier_obligation
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger boundaryLeft boundaryRight curvatureLeft curvatureRight : BHist} :
    CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB provenance
        ledgerA ledgerB boundary curvatureLedger ->
      hsame boundary boundaryLeft ->
        Cont boundaryLeft provenance curvatureLeft ->
          hsame boundary boundaryRight ->
            Cont boundaryRight provenance curvatureRight ->
              CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB
                  provenance ledgerA ledgerB boundaryLeft curvatureLeft ∧
                CurvatureBracketCarrier base fibre sec tangentA tangentB derivativeA derivativeB
                    provenance ledgerA ledgerB boundaryRight curvatureRight ∧
                  hsame curvatureLeft curvatureRight := by
  intro carrier sameLeft leftCont sameRight rightCont
  have leftTransport :=
    CurvatureBracketCarrier_classifier_transport_row carrier sameLeft leftCont
  have rightTransport :=
    CurvatureBracketCarrier_classifier_transport_row carrier sameRight rightCont
  have sameCurvature : hsame curvatureLeft curvatureRight :=
    hsame_trans (hsame_symm leftTransport.right) rightTransport.right
  exact And.intro leftTransport.left
    (And.intro rightTransport.left sameCurvature)

end BEDC.Derived.CurvatureUp
