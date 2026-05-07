import BEDC.Derived.CommRingUp
import BEDC.Derived.RingedSpaceUp
import BEDC.Derived.SheafUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp

def SchemeSingletonPackage
    (point openHist sectionHist germ ringEndpoint chartA chartB overlap : BHist) : Prop :=
  RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ∧
    CommRingSingletonClassifier chartA BHist.Empty ∧
      CommRingSingletonClassifier chartB BHist.Empty ∧
        SheafBHistPointGermComparison point openHist sectionHist germ openHist sectionHist germ
          overlap

theorem SchemeSingletonPackage_carrier_source_obligation
    {point openHist sectionHist germ ringEndpoint chartA chartB overlap tail : BHist} :
    SchemeSingletonPackage point openHist sectionHist germ ringEndpoint chartA chartB overlap ->
      RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ∧
        CommRingSingletonCarrier chartA ∧ CommRingSingletonCarrier chartB ∧
          SheafBHistPointGermComparison point openHist sectionHist germ openHist sectionHist germ
            overlap ∧
            (hsame overlap (BHist.e0 tail) -> False) := by
  intro package
  have overlapNotZero : hsame overlap (BHist.e0 tail) -> False := by
    intro sameZero
    exact unary_no_zero_extension
      (unary_transport package.right.right.right.right.right.right.left sameZero)
  exact And.intro package.left
    (And.intro package.right.left.left
      (And.intro package.right.right.left.left
        (And.intro package.right.right.right overlapNotZero)))

end BEDC.Derived.SchemeUp
