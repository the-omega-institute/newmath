import BEDC.Derived.SheafUp.IdentityCover

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.TopologyUp

theorem SheafBaseChangeIdentitySquare_restriction_neutrality
    {point openHist sectionHist germ identityOpen identityGerm directGerm : BHist} :
    TopologySingletonOpenAt BHist.Empty point ->
      SheafBHistPointGermLedger point openHist sectionHist germ ->
        Cont openHist BHist.Empty identityOpen ->
          Cont identityOpen sectionHist identityGerm ->
            Cont openHist sectionHist directGerm ->
              SheafBHistPointGermLedger point openHist sectionHist directGerm ∧
                hsame identityGerm directGerm ∧ hsame identityOpen openHist := by
  intro openPoint ledger identityOpenRow identityGermRow directRow
  have identityReadback :
      hsame identityOpen openHist ∧ hsame identityGerm germ ∧
        SheafBHistPointGermLedger point identityOpen sectionHist identityGerm :=
    SheafIdentityCover_restriction_readback openPoint ledger identityOpenRow identityGermRow
  have directLedger : SheafBHistPointGermLedger point openHist sectionHist directGerm :=
    And.intro ledger.left (And.intro ledger.right.left directRow)
  have sameDirect : hsame germ directGerm :=
    cont_deterministic ledger.right.right directRow
  exact And.intro directLedger
    (And.intro (hsame_trans identityReadback.right.left sameDirect) identityReadback.left)

end BEDC.Derived.SheafUp
