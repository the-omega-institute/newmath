import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Package

namespace BEDC.Derived.CauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def CauchyFilterPacket [AskSetup] [PackageSetup]
    (observations window threshold endpoints compatibility transport consumer provenance
      nameRow endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont observations window threshold ∧
    Cont threshold endpoints compatibility ∧
      Cont compatibility transport consumer ∧
        Cont consumer provenance nameRow ∧
          Cont nameRow BHist.Empty endpoint ∧
            PkgSig bundle endpoint pkg

theorem CauchyFilterPacket_window_refinement_transport [AskSetup] [PackageSetup]
    {observations window window' threshold threshold' endpoints compatibility transport consumer
      provenance nameRow endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hsame window window' ->
      hsame threshold threshold' ->
        CauchyFilterPacket observations window threshold endpoints compatibility transport consumer
          provenance nameRow endpoint bundle pkg ->
          CauchyFilterPacket observations window' threshold' endpoints compatibility transport consumer
            provenance nameRow endpoint bundle pkg := by
  intro sameWindow sameThreshold packet
  exact And.intro
    (cont_hsame_transport (hsame_refl observations) sameWindow sameThreshold packet.left)
    (And.intro
      (cont_hsame_transport sameThreshold (hsame_refl endpoints) (hsame_refl compatibility)
        packet.right.left)
      packet.right.right)

end BEDC.Derived.CauchyFilterUp
