import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def SheafRestrictedOpenCarrier
    (point openHist sectionHist germ restrictedOpen restrictedGerm : BHist) : Prop :=
  SheafBHistPointGermLedger point openHist sectionHist germ ∧
    hsame openHist restrictedOpen ∧ Cont restrictedOpen sectionHist restrictedGerm

theorem SheafRestrictedOpenCarrier_common_refinement
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB : BHist} :
    SheafRestrictedOpenCarrier point openHist sectionA germA restrictedOpen restrictedGermA ->
      SheafRestrictedOpenCarrier point openHist sectionB germB restrictedOpen restrictedGermB ->
        hsame germA germB ->
          exists common : BHist,
            hsame common restrictedOpen ∧
              SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                restrictedOpen sectionB restrictedGermB common ∧
                hsame restrictedGermA restrictedGermB := by
  intro carrierA carrierB sameGerm
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      carrierA.left carrierB.left sameGerm carrierA.right.left carrierA.right.right
      carrierB.right.right
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      descent.left descent.right.left descent.right.right).left
  exact Exists.intro restrictedOpen
    (And.intro (hsame_refl restrictedOpen) (And.intro comparison descent.right.right))

end BEDC.Derived.SheafUp
