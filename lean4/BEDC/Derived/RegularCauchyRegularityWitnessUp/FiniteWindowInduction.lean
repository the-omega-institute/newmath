import BEDC.Derived.RegularCauchyRegularityWitnessUp.NameCertObligations

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyRegularityWitness_finite_window_induction [AskSetup] [PackageSetup]
    {S mu j Omega R Q E H C P N windowRead readbackRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRegularityWitnessCarrier S mu j Omega R Q E H C P N bundle pkg ->
      Cont j Omega windowRead ->
        Cont windowRead R readbackRead ->
          Cont readbackRead Q toleranceRead ->
            Cont toleranceRead E sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory toleranceRead ∧ UnaryHistory sealRead ∧
                    PkgSig bundle N pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier windowRoute readbackRoute toleranceRoute sealRoute sealPkg
  obtain ⟨_sUnary, _muUnary, jUnary, omegaUnary, rUnary, qUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _sourceRoute, _carrierWindowRoute, _carrierReadbackRoute,
    _carrierSealRoute, _pkgP, pkgN⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed jUnary omegaUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary qUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary eUnary sealRoute
  exact ⟨windowUnary, readbackUnary, toleranceUnary, sealUnary, pkgN, sealPkg⟩

end BEDC.Derived.RegularCauchyRegularityWitnessUp
