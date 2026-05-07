import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

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
