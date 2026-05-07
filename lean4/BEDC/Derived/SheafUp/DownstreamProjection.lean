import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SheafRootFaceRead_downstream_projection_separation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      Cont restrictedOpen sectionA restrictedGermA ∧
        Cont restrictedOpen sectionB restrictedGermB ∧
          SheafRootFaceRead restrictedOpen restrictedGermA .localityGluingRefinement ∧
            SheafRootFaceRead restrictedOpen restrictedGermB .localityGluingRefinement ∧
              hsame chartEndpoint restrictedGermB := by
  intro scope
  have rows :=
    SheafDownstreamConsumer_carrier_scope (point := point) (openHist := openHist)
      (sectionA := sectionA) (sectionB := sectionB) (germA := germA) (germB := germB)
      (restrictedOpen := restrictedOpen) (restrictedGermA := restrictedGermA)
      (restrictedGermB := restrictedGermB) (chartEndpoint := chartEndpoint) scope
  exact And.intro rows.right.right.left
    (And.intro rows.right.right.right.left
      (And.intro
        (SheafRootFaceRead.localityGluingRefinement rows.right.right.left
          rows.right.right.right.left rows.right.right.right.right.left)
        (And.intro
          (SheafRootFaceRead.localityGluingRefinement rows.right.right.right.left
            rows.right.right.left (hsame_symm rows.right.right.right.right.left))
          rows.right.right.right.right.right)))

theorem SheafRootConsumerRingedSpaceProjection_semantic_name_certificate
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SemanticNameCert
          (fun endpoint : BHist =>
            SheafRootFaceRead restrictedOpen endpoint .restrictionRoute)
          (fun endpoint : BHist =>
            SheafRootFaceRead restrictedOpen endpoint .restrictionRoute)
          (fun endpoint : BHist =>
            SheafRootFaceRead restrictedOpen endpoint .restrictionRoute)
          hsame ∧
        SheafRootFaceRead restrictedOpen restrictedGermA .restrictionRoute ∧
          SheafRootFaceRead restrictedOpen restrictedGermB .restrictionRoute ∧
            hsame restrictedGermA restrictedGermB := by
  intro scope
  have rows :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              hsame restrictedGermA restrictedGermB ∧
                hsame chartEndpoint restrictedGermB :=
    SheafDownstreamConsumer_carrier_scope (point := point) (openHist := openHist)
      (sectionA := sectionA) (sectionB := sectionB) (germA := germA) (germB := germB)
      (restrictedOpen := restrictedOpen) (restrictedGermA := restrictedGermA)
      (restrictedGermB := restrictedGermB) (chartEndpoint := chartEndpoint) scope
  have readA : SheafRootFaceRead restrictedOpen restrictedGermA .restrictionRoute :=
    SheafRootFaceRead.restrictionRoute rows.right.right.left
  have readB : SheafRootFaceRead restrictedOpen restrictedGermB .restrictionRoute :=
    SheafRootFaceRead.restrictionRoute rows.right.right.right.left
  have cert :
      SemanticNameCert
        (fun endpoint : BHist => SheafRootFaceRead restrictedOpen endpoint .restrictionRoute)
        (fun endpoint : BHist => SheafRootFaceRead restrictedOpen endpoint .restrictionRoute)
        (fun endpoint : BHist => SheafRootFaceRead restrictedOpen endpoint .restrictionRoute)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro restrictedGermA readA
      · intro endpoint _carrier
        exact hsame_refl endpoint
      · intro endpoint endpoint' same
        exact hsame_symm same
      · intro endpoint endpoint' endpoint'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro endpoint endpoint' same carrier
        cases same
        exact carrier
    · intro _endpoint source
      exact source
    · intro _endpoint source
      exact source
  exact And.intro cert
    (And.intro readA
      (And.intro readB rows.right.right.right.right.left))

theorem SheafDownstreamConsumer_RingedSpace_boundary_rows
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
          restrictedOpen sectionB restrictedGermB restrictedOpen ∧
        hsame chartEndpoint restrictedGermB ∧ UnaryHistory restrictedOpen ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB := by
  intro scope
  have rows :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              hsame restrictedGermA restrictedGermB ∧
                hsame chartEndpoint restrictedGermB :=
    SheafDownstreamConsumer_carrier_scope (point := point) (openHist := openHist)
      (sectionA := sectionA) (sectionB := sectionB) (germA := germA) (germB := germB)
      (restrictedOpen := restrictedOpen) (restrictedGermA := restrictedGermA)
      (restrictedGermB := restrictedGermB) (chartEndpoint := chartEndpoint) scope
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    SheafBHistPointGermComparison_restricted_open_descent
      scope.left scope.right.left scope.right.right.left scope.right.right.right.left
      scope.right.right.right.right.left scope.right.right.right.right.right.left
  exact And.intro comparison
    (And.intro rows.right.right.right.right.right
      (And.intro rows.left.right.left
        (And.intro rows.right.right.left rows.right.right.right.left)))

end BEDC.Derived.SheafUp
