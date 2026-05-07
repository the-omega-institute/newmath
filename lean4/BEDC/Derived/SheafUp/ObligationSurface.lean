import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

end BEDC.Derived.SheafUp
