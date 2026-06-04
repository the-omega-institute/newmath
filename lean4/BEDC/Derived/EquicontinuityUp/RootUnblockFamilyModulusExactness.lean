import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootUnblockFamilyModulusExactness [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead familyRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg →
      Cont K F familyRead →
        Cont familyRead rho modulusRead →
          PkgSig bundle modulusRead pkg →
            UnaryHistory familyRead ∧ UnaryHistory modulusRead ∧ Cont K F familyRead ∧
              Cont familyRead rho modulusRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle modulusRead pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier familyRoute modulusRoute modulusPkg
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _radiusRoute, _handoffRoute, provenancePkg,
    _localNamePkg⟩ := carrier
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed unaryK unaryF familyRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed familyUnary unaryRho modulusRoute
  exact
    ⟨familyUnary, modulusUnary, familyRoute, modulusRoute, provenancePkg, modulusPkg⟩

end BEDC.Derived.EquicontinuityUp
