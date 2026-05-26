import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealPowerSeriesObligationCarrier [AskSetup] [PackageSetup]
    (A R B U T V Q E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory B ∧ UnaryHistory U ∧
    UnaryHistory T ∧ UnaryHistory V ∧ UnaryHistory Q ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont A T Q ∧ Cont R Q U ∧ Cont U V E ∧ PkgSig bundle P pkg

theorem RealPowerSeriesObligationCarrier_radius_obligation [AskSetup] [PackageSetup]
    {A R B U T V Q E H C P N partialRead testRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesObligationCarrier A R B U T V Q E H C P N bundle pkg ->
      Cont A T partialRead ->
        Cont R partialRead testRead ->
          Cont testRead V endpointRead ->
            PkgSig bundle endpointRead pkg ->
              UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory Q ∧
                UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory E ∧
                  UnaryHistory partialRead ∧ UnaryHistory testRead ∧
                    UnaryHistory endpointRead ∧ Cont A T partialRead ∧
                      Cont R partialRead testRead ∧ Cont testRead V endpointRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier partialRoute testRoute endpointRoute endpointPkg
  obtain ⟨aUnary, rUnary, _bUnary, uUnary, tUnary, vUnary, qUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _partialCarrierRoute, _testCarrierRoute,
    _endpointCarrierRoute, pPkg⟩ := carrier
  have partialUnary : UnaryHistory partialRead :=
    unary_cont_closed aUnary tUnary partialRoute
  have testUnary : UnaryHistory testRead :=
    unary_cont_closed rUnary partialUnary testRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed testUnary vUnary endpointRoute
  exact
    ⟨aUnary, rUnary, tUnary, qUnary, uUnary, vUnary, eUnary, partialUnary, testUnary,
      endpointUnary, partialRoute, testRoute, endpointRoute, pPkg, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
