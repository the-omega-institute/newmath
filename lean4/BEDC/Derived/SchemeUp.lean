import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp

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

theorem SchemeAffineCoverLedger_classifier_refinement_transport
    {point openHist midOpen restrictedOpen sectionHist germ midGerm restrictedGerm
      ringEndpoint chartEndpoint : BHist} :
    RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ->
      hsame openHist midOpen ->
        Cont midOpen sectionHist midGerm ->
          hsame midOpen restrictedOpen ->
            Cont restrictedOpen sectionHist restrictedGerm ->
              CommRingSingletonClassifier chartEndpoint BHist.Empty ->
                RingedSpaceSingletonSurface point restrictedOpen sectionHist restrictedGerm
                    chartEndpoint ∧
                  hsame germ restrictedGerm ∧ hsame midGerm restrictedGerm ∧
                    CommRingSingletonClassifier ringEndpoint chartEndpoint := by
  intro surface sameMid midRow sameRestricted restrictedRow chartClassifier
  have midExact :
      RingedSpaceSingletonSurface point midOpen sectionHist midGerm chartEndpoint ∧
        hsame germ midGerm ∧ CommRingSingletonClassifier ringEndpoint chartEndpoint :=
    SchemeAffineCoverLedger_restriction_exactness
      surface sameMid midRow chartClassifier
  have restrictedExact :
      RingedSpaceSingletonSurface point restrictedOpen sectionHist restrictedGerm
          chartEndpoint ∧
        hsame midGerm restrictedGerm ∧
          CommRingSingletonClassifier chartEndpoint chartEndpoint :=
    SchemeAffineCoverLedger_restriction_exactness
      midExact.left sameRestricted restrictedRow chartClassifier
  exact And.intro restrictedExact.left
    (And.intro (hsame_trans midExact.right.left restrictedExact.right.left)
      (And.intro restrictedExact.right.left midExact.right.right))

end BEDC.Derived.SchemeUp
