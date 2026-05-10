import BEDC.Derived.SheafUp.RootCoverDescent

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafRootCoverNerveExportSurface
    (ambient member overlap route germ point openHist sectionA sectionB restrictedGermA
      restrictedGermB chartEndpoint : BHist) : Prop :=
  SheafBHistCoverNerveLedger ambient member overlap route germ ∧
    SheafDownstreamConsumerScope point openHist sectionA sectionB germ germ overlap
      restrictedGermA restrictedGermB chartEndpoint ∧
      UnaryHistory ambient ∧ Cont overlap route germ ∧
        SheafRootFaceRead member ambient SheafRootFaceLanding.coverMembership

theorem SheafRootCoverNerveExportSurface_rows
    {ambient member overlap route germ point openHist sectionA sectionB restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafRootCoverNerveExportSurface ambient member overlap route germ point openHist
      sectionA sectionB restrictedGermA restrictedGermB chartEndpoint ->
        SheafBHistCoverNerveLedger ambient member overlap route germ ∧
          SheafDownstreamConsumerScope point openHist sectionA sectionB germ germ overlap
            restrictedGermA restrictedGermB chartEndpoint ∧
            Cont overlap route germ := by
  intro surface
  exact And.intro surface.left
    (And.intro surface.right.left surface.right.right.right.left)

end BEDC.Derived.SheafUp
