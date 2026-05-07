import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SheafRootThreshold_carrier_classifier_semantic_certificate
    {ambient member overlap route germ localRoute localGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      Cont member localRoute localGerm -> hsame route localRoute ->
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
        hsame :=
    SheafRestrictedOpenCarrier_semantic_name_certificate readback.left
  exact And.intro cert readback

end BEDC.Derived.SheafUp
