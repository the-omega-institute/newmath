import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SheafCoverGluingNameCert_export
    {ambient member overlap route germ localRoute localGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      Cont member localRoute localGerm ->
        hsame route localRoute ->
          SemanticNameCert
              (fun endpoint : BHist =>
                SheafBHistPointGermLedger ambient member localRoute endpoint)
              (fun endpoint : BHist =>
                SheafBHistPointGermLedger ambient member localRoute endpoint)
              (fun endpoint : BHist =>
                SheafBHistPointGermLedger ambient member localRoute endpoint)
              hsame ∧
            SheafBHistPointGermLedger ambient member localRoute localGerm ∧
              hsame germ localGerm := by
  intro ledger localRow sameRoute
  have readback :
      SheafBHistPointGermLedger ambient member localRoute localGerm ∧
        hsame germ localGerm :=
    SheafBHistCoverNerveLedger_gluing_readback ledger localRow sameRoute
  have cert :
      SemanticNameCert
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger ambient member localRoute endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger ambient member localRoute endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger ambient member localRoute endpoint)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro localGerm readback.left
      · intro endpoint _carrier
        exact hsame_refl endpoint
      · intro endpoint endpoint' same
        exact hsame_symm same
      · intro endpoint endpoint' endpoint'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro endpoint endpoint' same carrier
        exact And.intro carrier.left
          (And.intro carrier.right.left
            (cont_result_hsame_transport carrier.right.right same))
    · intro _endpoint source
      exact source
    · intro _endpoint source
      exact source
  exact And.intro cert (And.intro readback.left readback.right)

end BEDC.Derived.SheafUp
