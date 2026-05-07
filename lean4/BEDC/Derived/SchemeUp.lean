import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp
open BEDC.Derived.TopologyUp

theorem SchemeSingleton_affine_cover_ledger_exactness
    {point openHist sectionHist germ ringEndpoint chartEndpoint restrictedOpen
      restrictedGerm : BHist} :
    RingedSpaceSingletonSurface point openHist sectionHist germ ringEndpoint ->
      CommRingSingletonClassifier chartEndpoint BHist.Empty ->
        hsame openHist restrictedOpen -> Cont restrictedOpen sectionHist restrictedGerm ->
          RingedSpaceSingletonSurface point restrictedOpen sectionHist restrictedGerm
              chartEndpoint ∧
            CommRingSingletonClassifier chartEndpoint BHist.Empty ∧ hsame germ restrictedGerm := by
  intro surface chartClass sameOpen restrictedRow
  have readback :=
    SheafBHistPointGermLedger_restriction_readback surface.right.left sameOpen restrictedRow
  have restrictedOpenAt : TopologySingletonOpenAt restrictedOpen point :=
    And.intro (hsame_trans (hsame_symm sameOpen) surface.left.left) surface.left.right
  exact And.intro
    (And.intro restrictedOpenAt (And.intro readback.left chartClass))
    (And.intro chartClass readback.right)

end BEDC.Derived.SchemeUp
