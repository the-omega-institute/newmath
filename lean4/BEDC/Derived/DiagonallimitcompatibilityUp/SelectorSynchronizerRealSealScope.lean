import BEDC.Derived.DiagonallimitcompatibilityUp.FiniteObservationBudgetFactorization

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_selector_synchronizer_real_seal_scope
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector synchronizer request budget terminal realScope : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
        Cont selector dyadic synchronizer →
          Cont synchronizer readback request →
            Cont request realSeal budget →
              Cont budget cert terminal →
                Cont terminal realSeal realScope →
                  PkgSig bundle terminal pkg →
                    PkgSig bundle realScope pkg →
                      UnaryHistory selector ∧ UnaryHistory synchronizer ∧
                        UnaryHistory request ∧ UnaryHistory budget ∧
                          UnaryHistory terminal ∧ UnaryHistory realScope ∧
                            Cont diagonal windows selector ∧
                              Cont selector dyadic synchronizer ∧
                                Cont synchronizer readback request ∧
                                  Cont request realSeal budget ∧
                                    Cont budget cert terminal ∧
                                      Cont terminal realSeal realScope ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle terminal pkg ∧
                                            PkgSig bundle realScope pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalWindowsSelector selectorDyadicSynchronizer
    synchronizerReadbackRequest requestRealSealBudget budgetCertTerminal
    terminalRealSealScope terminalPkg realScopePkg
  have factorization :=
    DiagonalLimitCompatibilityCarrier_finite_observation_budget_factorization
      (diagonal := diagonal) (triangle := triangle) (sealRow := sealRow) (dyadic := dyadic)
      (windows := windows) (readback := readback) (realSeal := realSeal)
      (transport := transport) (route := route) (provenance := provenance) (cert := cert)
      (selector := selector) (synchronizer := synchronizer) (request := request)
      (budget := budget) (terminal := terminal) (bundle := bundle) (pkg := pkg)
      carrier diagonalWindowsSelector selectorDyadicSynchronizer synchronizerReadbackRequest
      requestRealSealBudget budgetCertTerminal terminalPkg
  obtain ⟨selectorUnary, synchronizerUnary, requestUnary, budgetUnary, terminalUnary,
    diagonalWindowsSelector', selectorDyadicSynchronizer', synchronizerReadbackRequest',
    requestRealSealBudget', budgetCertTerminal', provenancePkg, terminalPkg'⟩ := factorization
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _carrierProvenancePkg⟩ := carrier
  have realScopeUnary : UnaryHistory realScope :=
    unary_cont_closed terminalUnary realSealUnary terminalRealSealScope
  exact
    ⟨selectorUnary, synchronizerUnary, requestUnary, budgetUnary, terminalUnary,
      realScopeUnary, diagonalWindowsSelector', selectorDyadicSynchronizer',
      synchronizerReadbackRequest', requestRealSealBudget', budgetCertTerminal',
      terminalRealSealScope, provenancePkg, terminalPkg', realScopePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
