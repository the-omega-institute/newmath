import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem SheafRootThreshold_semantic_name_certificate
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SemanticNameCert
        (fun endpoint : BHist =>
          SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
            restrictedOpen restrictedGermA restrictedGermB endpoint)
        (fun endpoint : BHist =>
          SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
            restrictedOpen restrictedGermA restrictedGermB endpoint)
        (fun endpoint : BHist =>
          SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB
            restrictedOpen restrictedGermA restrictedGermB endpoint)
        hsame := by
  intro scope
  constructor
  · constructor
    · exact Exists.intro chartEndpoint scope
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro endpoint endpoint' same
      exact hsame_symm same
    · intro endpoint endpoint' endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      exact And.intro carrier.left
        (And.intro carrier.right.left
          (And.intro carrier.right.right.left
            (And.intro carrier.right.right.right.left
              (And.intro carrier.right.right.right.right.left
                (And.intro carrier.right.right.right.right.right.left
                  (hsame_trans (hsame_symm same)
                    carrier.right.right.right.right.right.right))))))
  · intro _endpoint source
    exact source
  · intro _endpoint source
    exact source

theorem SheafRootThreshold_gluing_refinement_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              Cont restrictedOpen sectionA globalA -> Cont restrictedOpen sectionB globalB ->
                SheafBHistPointGermComparison point restrictedOpen sectionA globalA
                  restrictedOpen sectionB globalB restrictedOpen ∧ hsame globalA globalB := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB globalACont globalBCont
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have sameGlobalA : hsame restrictedGermA globalA :=
    cont_deterministic restrictedA globalACont
  have sameGlobalB : hsame restrictedGermB globalB :=
    cont_deterministic restrictedB globalBCont
  have sameGlobal : hsame globalA globalB :=
    hsame_trans (hsame_symm sameGlobalA)
      (hsame_trans descent.right.right sameGlobalB)
  exact And.intro
    (And.intro descent.left.left
      (And.intro descent.left.right.left
        (And.intro descent.right.left.right.left
          (And.intro descent.left.right.left
            (And.intro (hsame_refl restrictedOpen)
              (And.intro (hsame_refl restrictedOpen)
                (And.intro globalACont
                  (And.intro globalBCont sameGlobal))))))))
    sameGlobal

end BEDC.Derived.SheafUp
