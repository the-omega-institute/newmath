import BEDC.Derived.CauchyContinuousExtensionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyContinuousExtensionUp

open BEDC.Derived.CauchyContinuousExtensionUp.TasteGate
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyExtensionUniformModulusSink [AskSetup] [PackageSetup]
    (S W D F U L H C P N sourceRead toleranceRead mapRead extensionRead replayRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  cauchyContinuousExtensionFields
        (CauchyContinuousExtensionUp.mk S W D F U L H C P N) =
      [S, W, D, F, U, L, H, C, P, N] ∧
    UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory F ∧
      UnaryHistory U ∧ UnaryHistory C ∧ Cont S W sourceRead ∧
        Cont sourceRead D toleranceRead ∧ Cont toleranceRead F mapRead ∧
          Cont mapRead U extensionRead ∧ Cont extensionRead C replayRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg

end BEDC.Derived.CauchyContinuousExtensionUp
