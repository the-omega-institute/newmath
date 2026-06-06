import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootCompactSourceAdmission [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead compactRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg →
      UnaryHistory M →
        UnaryHistory N →
          Cont handoffRead M compactRead →
            Cont compactRead N namedRead →
              PkgSig bundle namedRead pkg →
                UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory rho ∧
                  UnaryHistory radiusRead ∧ UnaryHistory handoffRead ∧
                    UnaryHistory compactRead ∧ UnaryHistory namedRead ∧
                      Cont K F radiusRead ∧ Cont radiusRead rho handoffRead ∧
                        Cont handoffRead M compactRead ∧ Cont compactRead N namedRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                            PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier unaryM unaryN compactRoute namedRoute namedPkg
  obtain ⟨radiusUnary, handoffUnary, _radiusRoute, _handoffRoute, _pkgP, _pkgN⟩ :=
    EquicontinuityCarrier_shared_radius_stability carrier
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _carrierUnaryN, radiusRoute, handoffRoute,
    pkgP, pkgN⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed handoffUnary unaryM compactRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed compactUnary unaryN namedRoute
  exact
    ⟨unaryK, unaryF, unaryRho, radiusUnary, handoffUnary, compactUnary, namedUnary,
      radiusRoute, handoffRoute, compactRoute, namedRoute, pkgP, pkgN, namedPkg⟩

end BEDC.Derived.EquicontinuityUp
