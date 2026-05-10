import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.TopologyUp

theorem SheafIdentityCover_restriction_readback
    {point openHist sectionHist germ identityOpen identityGerm : BHist} :
    TopologySingletonOpenAt BHist.Empty point ->
      SheafBHistPointGermLedger point openHist sectionHist germ ->
        Cont openHist BHist.Empty identityOpen ->
          Cont identityOpen sectionHist identityGerm ->
            hsame identityOpen openHist ∧ hsame identityGerm germ ∧
              SheafBHistPointGermLedger point identityOpen sectionHist identityGerm := by
  intro _openPoint ledger identityOpenRow identityGermRow
  have sameIdentityOpen : hsame identityOpen openHist :=
    cont_deterministic identityOpenRow (cont_right_unit openHist)
  have readback :
      SheafBHistPointGermLedger point identityOpen sectionHist identityGerm ∧
        hsame germ identityGerm :=
    SheafBHistPointGermLedger_restriction_readback
      ledger (hsame_symm sameIdentityOpen) identityGermRow
  exact And.intro sameIdentityOpen
    (And.intro (hsame_symm readback.right) readback.left)

end BEDC.Derived.SheafUp
