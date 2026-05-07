import BEDC.Derived.SheafUp.CommonRefinementSpan
import BEDC.Derived.SheafUp.RefinedCoverExactness

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SheafRestrictedOpenRefinement_exactness_export
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              SemanticNameCert
                (fun endpoint : BHist =>
                  SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
                (fun endpoint : BHist =>
                  SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
                (fun endpoint : BHist =>
                  SheafBHistPointGermLedger point restrictedOpen sectionA endpoint ∧
                    exists paired : BHist,
                      SheafBHistPointGermLedger point restrictedOpen sectionB paired ∧
                        hsame endpoint paired)
                hsame := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  constructor
  · constructor
    · exact Exists.intro restrictedGermA descent.left
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro _endpoint _endpoint' same
      exact hsame_symm same
    · intro _endpoint _endpoint' _endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      exact And.intro carrier.left
        (And.intro carrier.right.left
          (cont_result_hsame_transport carrier.right.right same))
  · intro _endpoint source
    exact source
  · intro endpoint source
    have pairedLedger : SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB :=
      descent.right.left
    have sameEndpointPaired : hsame endpoint restrictedGermB :=
      hsame_trans
        (cont_deterministic source.right.right descent.left.right.right)
        descent.right.right
    exact And.intro source
      (Exists.intro restrictedGermB (And.intro pairedLedger sameEndpointPaired))

theorem SheafNameCertRefinementExactness_export
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA restrictedGermB
      globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              hsame restrictedGermA restrictedGermB ->
                Cont openHist sectionA globalA ->
                  Cont openHist sectionB globalB ->
                    SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                      SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                        SheafBHistPointGermComparison point restrictedOpen sectionA
                          restrictedGermA restrictedOpen sectionB restrictedGermB
                          restrictedOpen ∧
                          hsame globalA globalB ∧
                            SemanticNameCert
                              (fun endpoint : BHist =>
                                SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
                              (fun endpoint : BHist =>
                                SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
                              (fun endpoint : BHist =>
                                SheafBHistPointGermLedger point restrictedOpen sectionA endpoint ∧
                                  exists paired : BHist,
                                    SheafBHistPointGermLedger point restrictedOpen sectionB paired ∧
                                      hsame endpoint paired)
                              hsame := by
  intro ledgerA ledgerB sameOpen restrictedA restrictedB sameRestricted globalACont
    globalBCont
  have exactRows :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
            restrictedOpen sectionB restrictedGermB restrictedOpen ∧
            hsame globalA globalB :=
    SheafRefinedCover_exactness_obligation ledgerA ledgerB sameOpen restrictedA restrictedB
      sameRestricted globalACont globalBCont
  have cert :
      SemanticNameCert
        (fun endpoint : BHist => SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point restrictedOpen sectionA endpoint ∧
            exists paired : BHist,
              SheafBHistPointGermLedger point restrictedOpen sectionB paired ∧
                hsame endpoint paired)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro restrictedGermA exactRows.left
      · intro endpoint _carrier
        exact hsame_refl endpoint
      · intro _endpoint _endpoint' same
        exact hsame_symm same
      · intro _endpoint _endpoint' _endpoint'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro endpoint endpoint' same carrier
        exact And.intro carrier.left
          (And.intro carrier.right.left
            (cont_result_hsame_transport carrier.right.right same))
    · intro _endpoint source
      exact source
    · intro endpoint source
      have sameEndpointRestricted : hsame endpoint restrictedGermB :=
        hsame_trans
          (cont_deterministic source.right.right exactRows.left.right.right)
          sameRestricted
      exact And.intro source
        (Exists.intro restrictedGermB
          (And.intro exactRows.right.left sameEndpointRestricted))
  exact And.intro exactRows.left
    (And.intro exactRows.right.left
      (And.intro exactRows.right.right.left
        (And.intro exactRows.right.right.right cert)))

theorem SheafBaseChange_common_refinement_composition
    {point common openA openB sectA sectB germA germB midCommon finalCommon midGermA
      midGermB finalGermA finalGermB : BHist} :
    SheafDisplayedCommonRefinementSpan point common openA openB sectA sectB germA germB ->
      hsame common midCommon ->
        Cont midCommon sectA midGermA ->
          Cont midCommon sectB midGermB ->
            hsame midCommon finalCommon ->
              Cont finalCommon sectA finalGermA ->
                Cont finalCommon sectB finalGermB ->
                  SheafDisplayedCommonRefinementSpan point finalCommon openA openB sectA sectB
                      finalGermA finalGermB ∧
                    hsame germA finalGermA ∧ hsame germB finalGermB ∧
                      hsame midGermA finalGermA ∧ hsame midGermB finalGermB := by
  intro span sameMid midA midB sameFinal finalA finalB
  have commonFinal : hsame common finalCommon :=
    hsame_trans sameMid sameFinal
  have finalCommonUnary : UnaryHistory finalCommon :=
    unary_transport span.right.left commonFinal
  have sameGermAFinal : hsame germA finalGermA :=
    cont_respects_hsame commonFinal (hsame_refl sectA)
      span.right.right.right.right.left finalA
  have sameGermBFinal : hsame germB finalGermB :=
    cont_respects_hsame commonFinal (hsame_refl sectB)
      span.right.right.right.right.right.left finalB
  have sameFinalGerms : hsame finalGermA finalGermB :=
    hsame_trans (hsame_symm sameGermAFinal)
      (hsame_trans span.right.right.right.right.right.right sameGermBFinal)
  have finalSpan :
      SheafDisplayedCommonRefinementSpan point finalCommon openA openB sectA sectB
        finalGermA finalGermB :=
    And.intro span.left
      (And.intro finalCommonUnary
        (And.intro (hsame_trans (hsame_symm commonFinal) span.right.right.left)
          (And.intro (hsame_trans (hsame_symm commonFinal) span.right.right.right.left)
            (And.intro finalA
              (And.intro finalB sameFinalGerms)))))
  have sameMidA : hsame midGermA finalGermA :=
    cont_respects_hsame sameFinal (hsame_refl sectA) midA finalA
  have sameMidB : hsame midGermB finalGermB :=
    cont_respects_hsame sameFinal (hsame_refl sectB) midB finalB
  exact And.intro finalSpan
    (And.intro sameGermAFinal
      (And.intro sameGermBFinal
        (And.intro sameMidA sameMidB)))

theorem SheafCoverPresentation_exactness
    {point common openA openB sectionA sectionB germA germB : BHist} :
    SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA germB ->
      SemanticNameCert
        (fun endpoint : BHist => SheafBHistPointGermLedger point common sectionA endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point common sectionA endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point common sectionA endpoint ∧
            exists paired : BHist,
              SheafBHistPointGermLedger point common sectionB paired ∧ hsame endpoint paired)
        hsame := by
  intro span
  have paired := SheafDisplayedCommonRefinementSpan_paired_refinements span
  have ledgerA :
      SheafBHistPointGermLedger point common sectionA germA :=
    paired.right.left
  have ledgerB :
      SheafBHistPointGermLedger point common sectionB germB :=
    paired.right.right
  have sameGerms : hsame germA germB :=
    span.right.right.right.right.right.right
  constructor
  · constructor
    · exact Exists.intro germA ledgerA
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro _endpoint _endpoint' same
      exact hsame_symm same
    · intro _endpoint _endpoint' _endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      exact And.intro carrier.left
        (And.intro carrier.right.left
          (cont_result_hsame_transport carrier.right.right same))
  · intro _endpoint source
    exact source
  · intro endpoint source
    have sameEndpointGermA : hsame endpoint germA :=
      cont_deterministic source.right.right ledgerA.right.right
    have sameEndpointGermB : hsame endpoint germB :=
      hsame_trans sameEndpointGermA sameGerms
    exact And.intro source
      (Exists.intro germB (And.intro ledgerB sameEndpointGermB))

theorem SheafBHistObligationSurface_restriction_cover_package
    {ambient member overlap route germ point openHist sectionA sectionB germA germB
      restrictedOpen restrictedGermA restrictedGermB localRoute localGerm tail : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB localGerm ->
        Cont member localRoute localGerm -> hsame route localRoute ->
          (hsame restrictedOpen (BHist.e0 tail) -> False) ∧
            SheafBHistPointGermLedger ambient member localRoute localGerm ∧
              SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                restrictedOpen sectionB restrictedGermB restrictedOpen ∧
                hsame germ localGerm ∧ hsame restrictedGermA restrictedGermB := by
  intro cover scope localRow sameRoute
  have downstreamRows :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              hsame restrictedGermA restrictedGermB ∧ hsame localGerm restrictedGermB :=
    SheafDownstreamConsumer_carrier_scope scope
  have restrictedOpenNotE0 : hsame restrictedOpen (BHist.e0 tail) -> False := by
    intro sameRestrictedOpen
    exact unary_history_hsame_zero_absurd downstreamRows.left.right.left sameRestrictedOpen
  have coverReadback :
      SheafBHistPointGermLedger ambient member localRoute localGerm ∧
        hsame germ localGerm :=
    SheafBHistCoverNerveLedger_gluing_readback cover localRow sameRoute
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    SheafBHistPointGermComparison_restricted_open_descent
      scope.left scope.right.left scope.right.right.left scope.right.right.right.left
      scope.right.right.right.right.left scope.right.right.right.right.right.left
  exact And.intro restrictedOpenNotE0
    (And.intro coverReadback.left
      (And.intro comparison
        (And.intro coverReadback.right downstreamRows.right.right.right.right.left)))

end BEDC.Derived.SheafUp
