import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SheafBHistPointGermComparison_locality_gluing_semantic_name_certificate
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              SemanticNameCert
                (fun endpoint : BHist =>
                  SheafBHistPointGermComparison point restrictedOpen sectionA endpoint
                    restrictedOpen sectionB restrictedGermB restrictedOpen)
                (fun endpoint : BHist =>
                  SheafBHistPointGermComparison point restrictedOpen sectionA endpoint
                    restrictedOpen sectionB restrictedGermB restrictedOpen)
                (fun endpoint : BHist =>
                  SheafBHistPointGermComparison point restrictedOpen sectionA endpoint
                    restrictedOpen sectionB restrictedGermB restrictedOpen)
                hsame := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    SheafBHistPointGermComparison_restricted_open_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  constructor
  · constructor
    · exact Exists.intro restrictedGermA comparison
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro endpoint endpoint' same
      exact hsame_symm same
    · intro endpoint endpoint' endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      have transportedA : Cont restrictedOpen sectionA endpoint' :=
        cont_result_hsame_transport
          carrier.right.right.right.right.right.right.left same
      have transportedGerm : hsame endpoint' restrictedGermB :=
        hsame_trans (hsame_symm same)
          carrier.right.right.right.right.right.right.right.right
      exact And.intro carrier.left
        (And.intro carrier.right.left
          (And.intro carrier.right.right.left
            (And.intro carrier.right.right.right.left
              (And.intro carrier.right.right.right.right.left
                (And.intro carrier.right.right.right.right.right.left
                  (And.intro transportedA
                    (And.intro carrier.right.right.right.right.right.right.right.left
                      transportedGerm)))))))
  · intro _endpoint source
    exact source
  · intro _endpoint source
    exact source

end BEDC.Derived.SheafUp
