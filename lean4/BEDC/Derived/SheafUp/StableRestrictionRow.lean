import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafStableRestrictionRow
    (point openHist sectionHist germ restrictedOpen restrictedGerm : BHist) : Prop :=
  SheafBHistPointGermLedger point openHist sectionHist germ ∧
    hsame openHist restrictedOpen ∧ Cont restrictedOpen sectionHist restrictedGerm

theorem SheafStableRestrictionRow_transport
    {point openHist sectionHist germ restrictedOpen restrictedGerm : BHist} :
    SheafStableRestrictionRow point openHist sectionHist germ restrictedOpen restrictedGerm ->
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame germ restrictedGerm ∧ UnaryHistory restrictedOpen := by
  intro row
  have readback :
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame germ restrictedGerm :=
    SheafBHistPointGermLedger_restriction_readback row.left row.right.left row.right.right
  exact And.intro readback.left (And.intro readback.right readback.left.right.left)

end BEDC.Derived.SheafUp
