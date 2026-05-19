import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RealityConstrainedTruthCertFailureReadiness [AskSetup] [PackageSetup]
    {F F' N failureName failureName' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hsame F F' ->
      Cont F N failureName ->
        Cont F' N failureName' ->
          PkgSig bundle failureName pkg ->
            PkgSig bundle failureName' pkg ->
              hsame failureName failureName' ∧
                Cont F N failureName ∧
                  Cont F' N failureName' ∧
                    PkgSig bundle failureName pkg ∧
                      PkgSig bundle failureName' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame
  intro sameFailure leftRoute rightRoute leftPkg rightPkg
  have sameName : hsame failureName failureName' :=
    cont_respects_hsame sameFailure (hsame_refl N) leftRoute rightRoute
  exact ⟨sameName, leftRoute, rightRoute, leftPkg, rightPkg⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
