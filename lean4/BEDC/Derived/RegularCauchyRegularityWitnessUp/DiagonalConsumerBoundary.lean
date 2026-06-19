import BEDC.Derived.RegularCauchyRegularityWitnessUp.NameCertObligations

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyRegularityWitnessDiagonalConsumerBoundary [AskSetup] [PackageSetup]
    {S mu j Omega R Q E H C P N diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRegularityWitnessCarrier S mu j Omega R Q E H C P N bundle pkg →
      Cont S Omega diagonalRead →
        PkgSig bundle diagonalRead pkg →
          UnaryHistory S ∧ UnaryHistory Omega ∧ UnaryHistory R ∧ UnaryHistory Q ∧
            UnaryHistory E ∧ UnaryHistory diagonalRead ∧ Cont S mu j ∧
              Cont j Omega R ∧ Cont R Q E ∧ Cont E H C ∧ PkgSig bundle P pkg ∧
                PkgSig bundle diagonalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier diagonalRoute diagonalPkg
  obtain ⟨unaryS, _unaryMu, _unaryJ, unaryOmega, unaryR, unaryQ, unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, routeSMuJ, routeJOmegaR, routeRQE, routeEHC,
    pkgP, _pkgN⟩ := carrier
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed unaryS unaryOmega diagonalRoute
  exact
    ⟨unaryS, unaryOmega, unaryR, unaryQ, unaryE, diagonalUnary, routeSMuJ,
      routeJOmegaR, routeRQE, routeEHC, pkgP, diagonalPkg⟩

end BEDC.Derived.RegularCauchyRegularityWitnessUp
