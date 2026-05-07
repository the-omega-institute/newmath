import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafStableRestrictionRow_endpoint_transport
    {point openHist sectionHist germ restrictedOpen restrictedGerm restrictedGerm' : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionHist restrictedGerm ->
          hsame restrictedGerm restrictedGerm' ->
            SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm' ∧
              hsame germ restrictedGerm' := by
  intro ledger sameOpen restrictedRow sameRestricted
  have readback :
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame germ restrictedGerm :=
    SheafBHistPointGermLedger_restriction_readback ledger sameOpen restrictedRow
  have transportedRow : Cont restrictedOpen sectionHist restrictedGerm' :=
    cont_result_hsame_transport restrictedRow sameRestricted
  exact And.intro
    (And.intro readback.left.left (And.intro readback.left.right.left transportedRow))
    (hsame_trans readback.right sameRestricted)

end BEDC.Derived.SheafUp
