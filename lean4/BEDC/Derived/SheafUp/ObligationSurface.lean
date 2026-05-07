import BEDC.Derived.SheafUp.ExactnessExport

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SheafBHistObligationSurface_cover_restriction_classifier
    {ambient member overlap route germ localRoute localGerm point openHist sectionA germA
      restrictedOpen restrictedGermA : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      Cont member localRoute localGerm ->
        hsame route localRoute ->
          SheafBHistPointGermLedger point openHist sectionA germA ->
            hsame openHist restrictedOpen ->
              hsame member restrictedOpen ->
                hsame localRoute sectionA ->
                  Cont restrictedOpen sectionA restrictedGermA ->
                    hsame localGerm restrictedGermA ∧
                      SheafBHistPointGermLedger point restrictedOpen sectionA
                        restrictedGermA ∧
                        hsame germ localGerm := by
  intro coverLedger localRow sameRoute pointLedger sameOpen sameMember sameLocalRoute
    restrictedRow
  have coverReadback :
      SheafBHistPointGermLedger ambient member localRoute localGerm ∧
        hsame germ localGerm :=
    SheafBHistCoverNerveLedger_gluing_readback coverLedger localRow sameRoute
  have localRestricted : hsame localGerm restrictedGermA :=
    cont_respects_hsame sameMember sameLocalRoute localRow restrictedRow
  have restrictedReadback :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        hsame germA restrictedGermA :=
    SheafBHistPointGermLedger_restriction_readback pointLedger sameOpen restrictedRow
  exact And.intro localRestricted
    (And.intro restrictedReadback.left coverReadback.right)

theorem SheafNameCert_obligation_surface
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB ambient member overlap route coverGerm localRoute localGerm tail :
        BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB localGerm ->
      SheafBHistCoverNerveLedger ambient member overlap route coverGerm ->
        Cont member localRoute localGerm ->
          hsame route localRoute ->
            SemanticNameCert
                (fun endpoint : BHist =>
                  SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
                (fun endpoint : BHist =>
                  SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
                (fun endpoint : BHist =>
                  SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
                hsame ∧
              SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                restrictedOpen sectionB restrictedGermB restrictedOpen ∧
                hsame coverGerm localGerm ∧
                  (hsame restrictedOpen (BHist.e0 tail) -> False) := by
  intro scope cover localRow sameRoute
  have package :
      (hsame restrictedOpen (BHist.e0 tail) -> False) ∧
        SheafBHistPointGermLedger ambient member localRoute localGerm ∧
          SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
            restrictedOpen sectionB restrictedGermB restrictedOpen ∧
            hsame coverGerm localGerm ∧ hsame restrictedGermA restrictedGermB :=
    SheafBHistObligationSurface_restriction_cover_package
      cover scope localRow sameRoute
  have downstream :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              hsame restrictedGermA restrictedGermB ∧
                hsame localGerm restrictedGermB :=
    SheafDownstreamConsumer_carrier_scope scope
  have cert :
      SemanticNameCert
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
        hsame :=
    SheafRestrictedOpenCarrier_semantic_name_certificate downstream.left
  exact And.intro cert
    (And.intro package.right.right.left
      (And.intro package.right.right.right.left package.left))

theorem SheafBHistCoverNerveLedger_exactness_obligation
    {ambient member overlap route germ localRoute localGerm nextRoute nextGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      Cont member localRoute localGerm ->
        hsame route localRoute ->
          UnaryHistory nextRoute ->
            Cont member nextRoute nextGerm ->
              SheafBHistPointGermLedger ambient member localRoute localGerm ∧
                hsame germ localGerm ∧
                  SheafBHistCoverNerveLedger ambient member member nextRoute nextGerm ∧
                    UnaryHistory nextGerm := by
  intro coverLedger localRow sameRoute nextRouteUnary nextRow
  have readback :
      SheafBHistPointGermLedger ambient member localRoute localGerm ∧
        hsame germ localGerm :=
    SheafBHistCoverNerveLedger_gluing_readback coverLedger localRow sameRoute
  have membership :
      SheafBHistCoverNerveLedger ambient member member nextRoute nextGerm ∧
        UnaryHistory nextGerm :=
    SheafRootCoverNerve_membership_exhaustion coverLedger nextRouteUnary nextRow
  exact And.intro readback.left
    (And.intro readback.right
      (And.intro membership.left membership.right))

end BEDC.Derived.SheafUp
