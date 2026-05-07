import BEDC.Derived.CommRingUp
import BEDC.Derived.RingedSpaceUp
import BEDC.Derived.SheafUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

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

theorem SchemeAffineCoverClassifier_overlap_locality
    {point openA openB sectionA sectionB germA germB ringA ringB chartA chartB common : BHist} :
    RingedSpaceSingletonSurface point openA sectionA germA ringA ->
      RingedSpaceSingletonSurface point openB sectionB germB ringB ->
        SheafBHistPointGermComparison point openA sectionA germA openB sectionB germB common ->
          CommRingSingletonClassifier chartA ringA ->
            CommRingSingletonClassifier chartB ringB ->
              hsame germA germB ∧ CommRingSingletonCarrier ringA ∧
                CommRingSingletonCarrier ringB := by
  intro _surfaceA _surfaceB comparison chartAClassified chartBClassified
  exact And.intro comparison.right.right.right.right.right.right.right.right
    (And.intro chartAClassified.right.left chartBClassified.right.left)

theorem SchemeSingleton_affine_cover_classifier_locality_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB ringEndpoint chartA chartB : BHist} :
    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpoint ->
      RingedSpaceSingletonSurface point openHist sectionB germB ringEndpoint ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              CommRingSingletonClassifier chartA chartB ->
                SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                    restrictedOpen sectionB restrictedGermB restrictedOpen ∧
                  CommRingSingletonClassifier chartA chartB ∧
                    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpoint ∧
                      RingedSpaceSingletonSurface point openHist sectionB germB ringEndpoint := by
  intro surfaceA surfaceB sameGerm sameOpen restrictedA restrictedB chartClassifier
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    SheafBHistPointGermComparison_restricted_open_descent
      surfaceA.right.left surfaceB.right.left sameGerm sameOpen restrictedA restrictedB
  exact And.intro comparison
    (And.intro chartClassifier
      (And.intro surfaceA surfaceB))

theorem SchemeAffineCoverLedger_exactness_obligation
    {point openHist sectionHist germ ringEndpoint chartEndpoint : BHist} :
    RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ->
      CommRingSingletonClassifier ringEndpoint chartEndpoint ->
        SheafBHistPointGermLedger point openHist sectionHist germ ∧
          Cont openHist sectionHist germ ∧
            CommRingSingletonCarrier ringEndpoint ∧
              CommRingSingletonCarrier chartEndpoint ∧
                hsame ringEndpoint chartEndpoint ∧ TopologySingletonOpenAt openHist point := by
  intro surface chartClassifier
  exact And.intro surface.right.left
    (And.intro surface.right.left.right.right
      (And.intro chartClassifier.left
        (And.intro chartClassifier.right.left
          (And.intro chartClassifier.right.right surface.left))))

theorem SchemeAffineCoverLedger_restriction_exactness
    {point openHist restrictedOpen sectionHist germ restrictedGerm ringEndpoint
      chartEndpoint : BHist} :
    RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionHist restrictedGerm ->
          CommRingSingletonClassifier chartEndpoint BHist.Empty ->
            RingedSpaceSingletonSurface point restrictedOpen sectionHist restrictedGerm
              chartEndpoint ∧ hsame germ restrictedGerm ∧
                CommRingSingletonClassifier ringEndpoint chartEndpoint := by
  intro surface sameOpen restrictedRow chartClassifier
  have ringClassifier : CommRingSingletonClassifier ringEndpoint chartEndpoint :=
    And.intro surface.right.right.left
      (And.intro chartClassifier.left
        (hsame_trans surface.right.right.right.right (hsame_symm chartClassifier.right.right)))
  have restricted :
      RingedSpaceSingletonSurface point restrictedOpen sectionHist restrictedGerm chartEndpoint ∧
        hsame germ restrictedGerm ∧ CommRingSingletonClassifier chartEndpoint BHist.Empty :=
    RingedSpaceSingletonSurface_restriction_exact_ledger
      surface sameOpen restrictedRow ringClassifier
  exact And.intro restricted.left (And.intro restricted.right.left ringClassifier)

end BEDC.Derived.SchemeUp
