import BEDC.Derived.RealityConstrainedModelAuditUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedModelAuditUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RealityConstrainedModelAuditStrengthRowTransport [BEDC.FKernel.Ask.AskSetup]
    [PackageSetup]
    {H Pi O M C T L F S S' strengthRead strengthRead' : BHist}
    {bundle : ProbeBundle BEDC.FKernel.Ask.ProbeName} {pkg : Pkg} :
    realityConstrainedModelAuditFields
        (RealityConstrainedModelAuditUp.mk H Pi O M C T L F S) =
      [H, Pi, O, M, C, T, L, F, S] →
      hsame S S' →
        Cont S H strengthRead →
          Cont S' H strengthRead' →
            PkgSig bundle strengthRead pkg →
              PkgSig bundle strengthRead' pkg →
                hsame strengthRead strengthRead' ∧ Cont S H strengthRead ∧
                  Cont S' H strengthRead' ∧ PkgSig bundle strengthRead pkg ∧
                    PkgSig bundle strengthRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro fields sameStrength strengthRoute transportedRoute pkgStrength pkgTransported
  cases fields
  have sameRead : hsame strengthRead strengthRead' :=
    cont_respects_hsame sameStrength (hsame_refl H) strengthRoute transportedRoute
  exact ⟨sameRead, strengthRoute, transportedRoute, pkgStrength, pkgTransported⟩

end BEDC.Derived.RealityConstrainedModelAuditUp
